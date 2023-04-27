Require Export Vars.
Set Bullet Behavior "Strict Subproofs".

(** Typechecking **)

(*Signature*)
(*
Record sig :=
  {
    sig_t : list typesym;
    sig_f: list funsym;
    sig_p: list predsym
  }.*)

(* Typing rules for types *)

(*NOTE (TODO): paper does not include vt_var case. This means
  that no types with type variables can ever be valid.
  Later, we rule out expressions with unbound type vars*)
Inductive valid_type : context -> vty -> Prop :=
  | vt_int: forall s,
    valid_type s vty_int
  | vt_real: forall s,
    valid_type s vty_real
  | vt_var: forall s v,
    valid_type s (vty_var v)
  | vt_tycons: forall s ts vs,
    In ts (sig_t s) ->
    length vs = length (ts_args ts) ->
    (forall x, In x vs -> valid_type s x) ->
    (*Forall (fun x => valid_type s x) vs ->*)
    valid_type s (vty_cons ts vs).
(*Notation "s '|-' t" := (valid_type s t) (at level 40).*)

(*Typing rules for patterns*)
Inductive pattern_has_type: context -> pattern -> vty -> Prop :=
  | P_Var: forall s x,
    valid_type s (snd x) ->
    pattern_has_type s (Pvar x) (snd x)
  | P_Wild: forall s ty,
    valid_type s ty ->
    pattern_has_type s Pwild ty
  | P_Constr: forall s (params : list vty) (ps : list pattern) (f: funsym),
    In f (sig_f s) ->
    Forall (valid_type s) params ->
    (*NOTE: NOT included in paper - is this implied elsewhere?*)
    valid_type s (f_ret f) ->
    length ps = length (s_args f) ->
    length params = length (s_params f) ->
    (* For all i, [nth i tms] has type [sigma(nth i (s_args f))], where
      sigma is the type substitution that maps f's type vars to [params] *)
    let sigma : vty -> vty := ty_subst (s_params f) params in
    (forall x, In x (combine ps (map (ty_subst (s_params f) params) 
      (s_args f))) ->
      pattern_has_type s (fst x) (snd x)) ->
    (* No free variables in common *)
    (forall i j d x, i < length ps -> j < length ps -> i <> j ->
      ~(In x (pat_fv (nth i ps d)) /\ In x (pat_fv (nth j ps d)))) ->
        pattern_has_type s (Pconstr f params ps) (sigma (f_ret f))
  | P_Or: forall s p1 p2 ty,
    pattern_has_type s p1 ty ->
    pattern_has_type s p2 ty ->
    (forall x, In x (pat_fv p1) <-> In x (pat_fv p2)) ->
    pattern_has_type s (Por p1 p2) ty
  | P_Bind: forall s x p,
    ~ In x (pat_fv p) ->
    pattern_has_type s p (snd x) ->
    pattern_has_type s (Pbind p x) (snd x).

(* Typing rules for terms *)
Inductive term_has_type: context -> term -> vty -> Prop :=
  | T_int: forall s z,
    term_has_type s (Tconst (ConstInt z)) vty_int
  | T_real: forall s r,
    term_has_type s (Tconst (ConstReal r)) vty_real
  | T_Var: forall s x,
    valid_type s (snd x) ->
    term_has_type s (Tvar x) (snd x)
  | T_Fun: forall s (params : list vty) (tms : list term) (f: funsym),
    In f (sig_f s) ->
    Forall (valid_type s) params ->
    (*NOTE: NOT included in paper - is this implied elsewhere?*)
    valid_type s (f_ret f) ->
    length tms = length (s_args f) ->
    length params = length (s_params f) ->
    (* For all i, [nth i tms] has type [sigma(nth i (s_args f))], where
      sigma is the type substitution that maps f's type vars to [params] *)
    Forall (fun x => term_has_type s (fst x) (snd x)) (combine tms
      (map (ty_subst (s_params f) params) (s_args f))) ->
    term_has_type s (Tfun f params tms) (ty_subst (s_params f) params (f_ret f))
  | T_Let: forall s t1 x t2 ty2,
    term_has_type s t1 (snd x) ->
    term_has_type s t2 ty2 ->
    term_has_type s (Tlet t1 x t2) ty2
  | T_If: forall s f t1 t2 ty,
    valid_formula s f ->
    term_has_type s t1 ty ->
    term_has_type s t2 ty ->
    term_has_type s (Tif f t1 t2) ty
  | T_Match: forall s tm ty1 (ps: list (pattern * term)) ty2,
    (*A pattern match matches on an algebraic datatype*)
    (exists a m args, mut_in_ctx m s /\
      adt_in_mut a m /\
      ty1 = vty_cons (adt_name a) args) ->
    term_has_type s tm ty1 ->
    (forall x, In x ps -> pattern_has_type s (fst x) ty1) ->
    (forall x, In x ps -> term_has_type s (snd x) ty2) ->
    (*Makes things MUCH simpler to include this - TODO: is this a problem?
    If not, need to prove by knowing that pattern matching exhaustive, so
    nonempty, so can take 1st element. But then we need a context
    and additional hypotheses in semantics.*)
    (*valid_type s ty2 ->*)
    (*need this to ensure that typing is decidable*)
    negb (null ps) ->
    term_has_type s (Tmatch tm ty1 ps) ty2
  | T_eps: forall s x f,
    (*TODO: is this the right typing rule?*)
    valid_formula s f ->
    valid_type s (snd x) ->
    term_has_type s (Teps f x) (snd x)


(* Typing rules for formulas *)
with valid_formula: context -> formula -> Prop :=
  | F_True: forall s,
    valid_formula s Ftrue
  | F_False: forall s,
    valid_formula s Ffalse
  | F_Binop: forall s b f1 f2,
    valid_formula s f1 ->
    valid_formula s f2 ->
    valid_formula s (Fbinop b f1 f2)
  | F_Not: forall s f,
    valid_formula s f ->
    valid_formula s (Fnot f)
  | F_Quant: forall s q x f,
    valid_type s (snd x) ->
    valid_formula s f ->
    valid_formula s (Fquant q x f)
  | F_Pred: forall s (params: list vty) (tms: list term) (p: predsym),
    (*Very similar to function case*)
    In p (sig_p s) ->
    Forall (valid_type s) params ->
    length tms = length (s_args p) ->
    length params = length (s_params p) ->
    Forall (fun x => term_has_type s (fst x) (snd x))
      (combine tms (map (ty_subst (s_params p) params) (s_args p))) ->
    valid_formula s (Fpred p params tms)
  | F_Let: forall s t x f,
    term_has_type s t (snd x) ->
    valid_formula s f ->
    valid_formula s (Flet t x f)
  | F_If: forall s f1 f2 f3,
    valid_formula s f1 ->
    valid_formula s f2 ->
    valid_formula s f3 ->
    valid_formula s (Fif f1 f2 f3)
  | F_Eq: forall s ty t1 t2,
    term_has_type s t1 ty ->
    term_has_type s t2 ty ->
    valid_formula s (Feq ty t1 t2)
  | F_Match: forall s tm ty (ps: list (pattern * formula)),
    (exists a m args, mut_in_ctx m s /\
    adt_in_mut a m /\
    ty = vty_cons (adt_name a) args) ->
    term_has_type s tm ty ->
    (forall x, In x ps -> pattern_has_type s (fst x) ty) ->
    (forall x, In x ps -> valid_formula s (snd x)) ->
    (*See comment in term*)
    negb (null ps) ->
    valid_formula s (Fmatch tm ty ps).
(*
Notation "s '|-' t ':' ty" := (term_has_type s t ty) (at level 40).
Notation "s '|-' f" := (valid_formula s f) (at level 40).*)

Lemma bool_dec: forall {A: Type} (f: A -> bool),
  (forall x : A, {is_true (f x)} + {~ is_true (f x)}).
Proof.
  intros A f x. destruct (f x) eqn : Hfx; auto.
Qed.

(*First, try this: TODO move*)
Lemma fun_ty_inversion: forall s (f: funsym) (vs: list vty) (tms: list term) ty_ret,
  term_has_type s (Tfun f vs tms) ty_ret ->
  In f (sig_f s) /\ Forall (valid_type s) vs /\
  length tms = length (s_args f) /\
  length vs = length (s_params f) /\
  Forall (fun x => term_has_type s (fst x) (snd x)) 
    (combine tms (map (ty_subst (s_params f) vs) (s_args f))) /\
  ty_ret = ty_subst (s_params f) vs (f_ret f).
Proof.
  intros. inversion H; subst; repeat split; auto.
Qed.

Lemma pred_ty_inversion: forall s (p: predsym) (vs: list vty) (tms: list term),
  valid_formula s (Fpred p vs tms) ->
  In p (sig_p s) /\ Forall (valid_type s) vs /\
  length tms = length (s_args p) /\
  length vs = length (s_params p) /\
  Forall (fun x => term_has_type s (fst x) (snd x)) 
    (combine tms (map (ty_subst (s_params p) vs) (s_args p))).
Proof.
  intros. inversion H; subst; repeat split; auto.
Qed.

Lemma valid_type_subst: forall s ty vars tys,
  valid_type s ty ->
  Forall (valid_type s) tys ->
  valid_type s (ty_subst vars tys ty).
Proof.
  intros. induction H; unfold ty_subst; simpl; try constructor; auto.
  - destruct (in_dec typevar_eq_dec v vars).
    + (*TODO: separate lemma (w no assumptions)*) 
      assert (In (ty_subst_fun vars tys vty_int v) tys \/ 
      (ty_subst_fun vars tys vty_int v) = vty_int
        ). {
        clear -i.
        revert tys. induction vars; simpl; intros.
        destruct i.
        destruct tys; auto.
        destruct (typevar_eq_dec v a); subst; simpl; auto.
        rewrite or_assoc. simpl in i. destruct i;
        subst; auto. contradiction.  
      }
      destruct H.
      * rewrite Forall_forall in H0; apply H0; auto.
      * rewrite H. constructor.
    + rewrite ty_subst_fun_notin; auto. constructor.
  - rewrite map_length. apply H1.
  - intros x. rewrite in_map_iff. intros [x1 [Hx1 Hinx1]].
    specialize (H3 _ Hinx1 H0). subst. apply H3.
Qed.

(*Now we define valid contexts. Unlike the paper,
  we combine signatures and contexts together so that
  we know which definitions are concrete and which are
  abstract. There are two parts: conditions each definition
  must satisfy, and some uniqueness conditions
  *)

(*First, well-formed fun/pred syms are those for which
  all type parameters appear in the arguments*)
Definition wf_funsym (gamma: context) (f: funsym) : Prop :=
  Forall (fun (t : vty) => valid_type gamma t /\
    Forall (fun fv => In fv (s_params f)) (type_vars t))
    (f_ret f :: s_args f).

Definition wf_predsym (gamma: context) (p: predsym) : Prop :=
  Forall (fun (t : vty) => valid_type gamma t /\
    Forall (fun fv => In fv (s_params p)) (type_vars t))
    (s_args p).

(** Algebraic Data Types **)
Section ValidMut.

(*We require that all type variables in mutually recursive types
  are correct: all component types and constructors have the same
  parameters*)
Definition valid_mut_rec (m: mut_adt) : Prop :=
  Forall (fun a => (m_params m) = (ts_args (adt_name a)) /\
    Forall (fun (f: funsym) => (m_params m) = (s_params f)) 
      (adt_constr_list a)) (typs m).


(*For an algebraic datatype to be valid, the following must hold:
  1. All constructors must have the correct type and type parameters
  2. The type must be inhabited (there must be 1 constructor with
    only inhabited types)
  3. Instances of the type must appear in strictly positive positions 
  We additionally require that all ADTs are uniform
  *)

(*Types*)
(*All constructors have the correct return type and the same parameters as
  the declaration*)
Definition adt_valid_type (a : alg_datatype) : Prop :=
  match a with
  | alg_def ts constrs => 
    Forall (fun (c: funsym) => 
      (s_params c) = (ts_args ts) /\ 
      (f_ret c) = vty_cons ts (map vty_var (ts_args ts))) 
        (ne_list_to_list constrs)
  end.
  
(*Inhabited types*)
Section Inhab.

Variable gamma: context.
(*Variable gamma_wf: wf_context gamma.*)

(*TODO: do this for real*)
(*This is more complicated than it seems, for 2 reasons:
1. Whether a type symbol/type is inhabited depends on the current context. For
  instance, we cannot assume that a recursive instance of a type is inhabited,
  but we can assume that previously-declared types are. Similarly, if we know
  that a type variable a is applied to a nonexistent type, we cannot assume
  further instances of a are inhabited. So we need 2 lists representing the
  known non-inhabited types in the current context.
2. The cons case in vty_inhab involes a condition: In x new_tvs <-> ~ vty_inhab _ _ y.
    This is not strictly positive, so we include an additional boolean parameter
    to indicate truth or falsehood. Thus, we need to add all the "false" cases,
    which otherwise would not be needed. It remains to show that this relation is
    decidable and that the boolean parameter correctly shows whether 
    *_inhab tss tvs x true is provable. *)
Unset Elimination Schemes.
Inductive typesym_inhab : list typesym -> list typevar -> typesym -> bool -> Prop :=
  | ts_check_empty: forall tss tvs ts,
    ~ In ts (sig_t gamma) ->
    typesym_inhab tss tvs ts false
  | ts_check_rec: forall tss tvs ts, (*recursive type*)
    In ts tss ->
    typesym_inhab tss tvs ts false
  | ts_check_typeT: forall tss tvs ts, (*for abstract type*)
    ~ In ts tss ->
    ~ In ts (map fst (datatypes_of_context gamma)) ->
    In ts (sig_t gamma) ->
    (*no "bad" type variables in context - these are the uninhabited arguments of the
      typesym (see vty_inhab below)*)
    null tvs ->
    typesym_inhab tss tvs ts true
  | ts_check_typeF: forall tss tvs ts,
    ~In ts tss  ->
    ~ In ts (map fst (datatypes_of_context gamma)) ->
    negb (null tvs) ->
    typesym_inhab tss tvs ts false
  | ts_check_adtT: forall tss tvs ts constrs c, (*for ADTs*)
    In ts (sig_t gamma) ->
    ~In ts tss ->
    In (ts, constrs) (datatypes_of_context gamma) ->
    negb (null constrs) ->
    In c constrs ->
    (constr_inhab (ts :: tss) tvs c true) ->
    typesym_inhab tss tvs ts true
  | ts_check_adtF1: forall tss tvs ts constrs,
    ~In ts tss ->
    In (ts, constrs) (datatypes_of_context gamma) ->
    null constrs ->
    typesym_inhab tss tvs ts false
  | ts_check_adtF2: forall tss tvs ts constrs,
    ~In ts tss ->
    In (ts, constrs) (datatypes_of_context gamma) ->
    negb( null constrs) ->
    (forall c, In c constrs -> constr_inhab (ts :: tss) tvs c false) ->
    typesym_inhab tss tvs ts false
with constr_inhab: list typesym -> list typevar -> funsym -> bool -> Prop :=
  | constr_checkT: forall tss tvs (c: funsym),
    (forall x, In x (s_args c) -> vty_inhab tss tvs x true) ->
    constr_inhab tss tvs c true
  | constr_checkF: forall tss tvs (c: funsym) v,
    In v (s_args c) ->
    vty_inhab tss tvs v false ->
    constr_inhab tss tvs c false
(*Here, need bool to deal with strict positivity issues*)
with vty_inhab: list typesym -> list typevar -> vty -> bool -> Prop :=
  | vty_check_int: forall tss tvs,
    vty_inhab tss tvs vty_int true
  | vty_check_real: forall tss tvs,
    vty_inhab tss tvs vty_real true
  | vty_check_varT: forall tss tvs tv,
    ~ In tv tvs ->
    vty_inhab tss tvs (vty_var tv) true
  | vty_check_varF: forall tss tvs tv,
    In tv tvs ->
    vty_inhab tss tvs (vty_var tv) false
  | vty_check_consT: forall tss tvs new_tvs ts args,
    (*making this condition strictly positive is not easy*)
    (*Condition: for all x y, In (x, y) (combine (ts_args ts) args) ->
    In x new_tvs <-> ~vty_inhab tss tvs y*)
    (forall x y, In (x, y) (combine args (ts_args ts)) ->
    ~ (In y new_tvs) -> vty_inhab tss tvs x true) ->
    (forall x y, In (x, y) (combine args (ts_args ts)) ->
      In y new_tvs -> vty_inhab tss tvs x false) ->
    typesym_inhab tss new_tvs ts true ->
    vty_inhab tss tvs (vty_cons ts args) true
  | vty_check_consF: forall tss tvs new_tvs ts args,
    (forall x y, In (x, y) (combine args (ts_args ts)) ->
    ~ (In y new_tvs) -> vty_inhab tss tvs x true) ->
    (forall x y, In (x, y) (combine args (ts_args ts)) ->
      In y new_tvs -> vty_inhab tss tvs x false) ->
    typesym_inhab tss new_tvs ts false ->
    vty_inhab tss tvs (vty_cons ts args) false
    .

Scheme typesym_inhab_ind := Minimality for typesym_inhab Sort Prop with
constr_inhab_ind := Minimality for constr_inhab Sort Prop with
vty_inhab_ind := Minimality for vty_inhab Sort Prop.

Set Elimination Schemes.

(*An ADT is inhabited if its typesym is inhabited under the empty context*)
Definition adt_inhab (a : alg_datatype) : Prop :=
  match a with
  | alg_def ts constrs => typesym_inhab nil nil ts true
  end.

(*We want to prove that this definition corresponds to (closed) types being inhabited.
  TODO: is it actually equivalent?*)

Definition find_constrs (gamma:context) (t: typesym) : option (list funsym) :=
  fold_right (fun x acc => if typesym_eq_dec (fst x) t then Some (snd x) else acc)
    None (datatypes_of_context gamma).

Lemma find_constrs_none: forall gamma t,
  find_constrs gamma t = None <-> ~In t (map fst (datatypes_of_context gamma)).
Proof.
  intros. unfold find_constrs. induction (datatypes_of_context gamma0); simpl; split; intros; auto.
  - destruct (typesym_eq_dec (fst a) t); [inversion H |].
    apply IHl in H. intro C. destruct C; auto.
  - destruct (typesym_eq_dec (fst a) t).
    + exfalso. apply H. left; auto.
    + apply IHl. intro C. apply H. right; auto.
Qed.

Lemma find_constrs_some: forall gamma t cs,
  NoDup (typesyms_of_context gamma) ->
  find_constrs gamma t = Some cs <-> In (t, cs) (datatypes_of_context gamma).
Proof.
  unfold typesyms_of_context, find_constrs. intros.
  induction (datatypes_of_context gamma0); simpl; split; intros; auto; try (solve [inversion H0]).
  - destruct (typesym_eq_dec (fst a) t); simpl; subst.
    + inversion H0; subst. left. destruct a; reflexivity.
    + apply IHl in H0. right; auto. simpl in H. inversion H; auto.
  - destruct H0; subst; simpl.
    + destruct (typesym_eq_dec t t); auto. contradiction.
    + destruct (typesym_eq_dec (fst a) t); subst; simpl.
      * simpl in H. inversion H; subst. exfalso. apply H3.
        rewrite in_map_iff. exists (fst a, cs). split; auto.
      * apply IHl; auto. inversion H; auto.
Qed.

(*For now, we assume this as an axiom*)
(*
Lemma adt_inhab_inhab: forall a,
  adt_in_ctx a gamma ->
  adt_inhab a ->
  forall vs,
    length vs = length (ts_args (adt_name a)) ->
    exists t, term_has_type s t (vty_cons (adt_name a) vs).
Admitted.*)

End Inhab.

(*Strict Positivity for Types*)

Fixpoint typesym_in (t: typesym) (v: vty) : bool :=
  match v with
  | vty_int => false
  | vty_real => false
  | vty_var x => false
  | vty_cons ts vs => typesym_eq_dec t ts || existsb (typesym_in t) vs
  end.

Section PosTypes.

(*harder because we dont have function types - need to mention constructor,
  not just type*)
(*Adapted from https://coq.inria.fr/refman/language/core/inductive.html*)

Variable gamma: context.
Unset Elimination Schemes.
Inductive strictly_positive : vty -> list typesym -> Prop :=
  | Strict_notin: forall (t: vty) (ts: list typesym),
    (forall x, In x ts -> negb(typesym_in x t)) ->
    strictly_positive t ts
  | Strict_constr: forall (t: vty) (ts: list typesym),
    (exists (x: typesym) vs, In x ts /\ t = vty_cons x vs /\
      (forall (y: typesym) (v: vty), In y ts -> In v vs ->
        negb (typesym_in y v))) ->
    strictly_positive t ts
  (*TODO: I don't think the 3rd case applies to us because
    we don't have built in function types -  how to handle function types?
    should we add function types? Then we need application and lambdas*)
  | Strict_ind: forall (t: vty) (ts: list typesym) (I: typesym) 
    (constrs: ne_list funsym) (vs: list vty),
    mut_typs_in_ctx [alg_def I constrs] gamma -> (*singleton list means non-mutually recursive*)
    t = vty_cons I vs ->
    (forall (x: typesym) (v: vty), In x ts -> In v vs ->
      negb (typesym_in x v)) ->
    (forall (c: funsym), In c (ne_list_to_list constrs) ->
      nested_positive c (ts_args I) vs I ts) ->
    strictly_positive t ts

(*I believe this reduces to positive in our case, but it only applies
  to non-mutual inductive types. How to encode this?*)
(*We don't have to worry about uniform/non-uniform params because
  our only params are type variables*)
(*We say constructor T of (non-mutual) inductive type I is satisfies
  nested positivity wrt ts*)
(*We take in the type substitution (params_i -> substs_i) (or [p_j/a_j])
  because this has to operate on a funsym, not a vty, since we don't have
  function types. This makes the definition a bit ugly*)
with nested_positive: funsym -> list typevar -> list vty ->
    typesym -> list typesym -> Prop :=
  | Nested_constr: forall (T: funsym) (params: list typevar) (substs: list vty)
      (I: typesym) (ts: list typesym),
    (forall vty, In vty (s_args T) -> 
      strictly_positive (ty_subst params substs vty) ts) ->
    (exists vs, (ty_subst params substs (f_ret T)) = vty_cons I vs /\
      (forall x v, In x ts -> In v vs -> negb (typesym_in x v))) ->
    nested_positive T params substs I ts.
Set Elimination Schemes.

Scheme strictly_positive_ind := Minimality for strictly_positive Sort Prop
with nested_positive_ind := Minimality for nested_positive Sort Prop.

Inductive positive : funsym -> list typesym -> Prop :=
  (*We combine into one case because of we don't have true function types*)
  | Pos_constr: forall (constr: funsym) (ts: list typesym),
    (forall vty, In vty (s_args constr) -> strictly_positive vty ts) ->
    (exists t vtys, In t ts /\ f_ret constr = vty_cons t vtys /\
      forall (v: vty) (x: typesym), In x ts -> In v vtys ->
        negb (typesym_in x v)) ->
    positive constr ts.

(*Finally, we want to say the following well-formedness condition:*)
Definition adt_positive (l: list alg_datatype) : Prop :=
  let ts : list typesym :=
    map (fun a => match a with | alg_def ts _ => ts end) l in
  let fs: list funsym :=
    concat (map (fun a => match a with | alg_def _ constrs => ne_list_to_list constrs end) l) in
  Forall (fun f => positive f ts) fs.

End PosTypes.

(*We also require that all mutually recursive types are uniform.
  Otherwise, inductive types become very difficult to define.
  Similarly, we require recursive functions and inductive predicates
  to be uniform; our semantics would get much more complicated if
  we allowed non-uniformity*)
Section UniformADT.


(*TODO: see where to add assumption, maybe prop version*)
Definition uniform_list (m: mut_adt) (l: list vty) : bool :=
  (forallb (fun v =>
        match v with
        | vty_cons ts vs => implb (ts_in_mut_list ts (typs m))
            (list_eq_dec vty_eq_dec vs 
              (map vty_var (m_params m)))
        | _ => true
        end
        )
  ) l. 

Lemma uniform_list_cons: forall {m hd tl},
  uniform_list m (hd :: tl) ->
  uniform_list m tl.
Proof.
  intros. clear -H. unfold uniform_list in *.
  unfold is_true in *. rewrite forallb_forall.
  rewrite forallb_forall in H.
  intros. apply H. right; auto.
Qed.
  
Definition uniform (m: mut_adt) : bool :=
  forallb (fun a => 
    forallb (fun (f: funsym) =>
      uniform_list m (s_args f) 
    ) (ne_list_to_list (adt_constrs a))
  ) (typs m).

End UniformADT.

(*And the final condition for mutual types*)
Definition mut_valid gamma m :=
  Forall adt_valid_type (typs m) /\ 
  Forall (adt_inhab gamma) (typs m) /\
  adt_positive gamma (typs m) /\
  valid_mut_rec m /\
  uniform m.

Section RecursiveDefs.

Variable gamma: context.

(* Recursive Functions and Predicates *)
Section RecFun.

(*This is complicated; we need to enforce a number of conditions.
  First, we bundle up the recursive function/predicate into a structure
  with its relevant information (this lets us define the 
  function/pred more conveniently)*)

(*First, we define how to get the "smaller" variables*)
Section SmallVar.

(*All variables from a pattern that are strictly "smaller" than
  the matched value*)
(*Inside a constructor: keep all variables of correct type *)
(*Gets all vars known to be decreasing (not strictly decreasing)*)
Fixpoint pat_constr_vars_inner (m: mut_adt) (vs: list vty) (p: pattern)
  {struct p} : list vsymbol :=
  match p with
  | Pconstr c tys ps =>
    if constr_in_m c m &&
    list_eq_dec vty_eq_dec tys vs &&
    (length ps =? length (s_args c)) then
    (*Only take those where the s_args is in m
      or else we get extra vsymbols which are not necessarily
      smaller (like the head in list)*)
    ((fix constr_inner (ps: list pattern) (vs': list vty) : list vsymbol :=
      match ps, vs' with
      | p1 :: p2, v1 :: v2 => 
        (*NOTE: we want type v1 to have type t(a, b, ...) NOT
        t(vs) - since this is in the constructor*)
        if vty_in_m m (map vty_var (m_params m)) v1 then
        union vsymbol_eq_dec (pat_constr_vars_inner m vs p1) (constr_inner p2 v2)
        else constr_inner p2 v2
      | _, _ => nil
      end    
    ) ps (s_args c))
    else nil
  | Por p1 p2 =>
    intersect vsymbol_eq_dec (pat_constr_vars_inner m vs p1)
      (pat_constr_vars_inner m vs p2)
  (*Only add variables of correct type*)
  | Pbind p' y =>
    union vsymbol_eq_dec (if vsym_in_m m vs y then [y] else nil)
      (pat_constr_vars_inner m vs p')
  | Pvar y =>
    if vsym_in_m m vs y then [y] else nil
  | Pwild => nil
  end.

(*rewrite lemma*)
Lemma pat_constr_vars_inner_eq (m: mut_adt) (vs: list vty) (p: pattern):
  pat_constr_vars_inner m vs p =
  match p with
  | Pconstr c tys ps =>
    if constr_in_m c m &&
    list_eq_dec vty_eq_dec tys vs &&
    (length ps =? length (s_args c)) then
    big_union vsymbol_eq_dec (pat_constr_vars_inner m vs)
      (map fst (filter (fun (x: pattern * vty) => 
        vty_in_m m (map vty_var (m_params m)) (snd x)) (combine ps (s_args c))))
    else nil
  | Por p1 p2 =>
    intersect vsymbol_eq_dec (pat_constr_vars_inner m vs p1)
      (pat_constr_vars_inner m vs p2)
  (*Only add variables of correct type*)
  | Pbind p' y =>
    union vsymbol_eq_dec (if vsym_in_m m vs y then [y] else nil)
      (pat_constr_vars_inner m vs p')
  | Pvar y =>
    if vsym_in_m m vs y then [y] else nil
  | Pwild => nil
  end.
Proof.
  unfold pat_constr_vars_inner at 1.
  destruct p; auto.
  destruct (constr_in_m f m); simpl; auto.
  destruct (list_eq_dec vty_eq_dec l vs); simpl; auto.
  destruct (length l0 =? length (s_args f)) eqn : Hlen; simpl; auto.
  apply Nat.eqb_eq in Hlen.
  generalize dependent (s_args f). subst. induction l0;
  intros; destruct l; inversion Hlen; simpl; auto.
  destruct (vty_in_m m (map vty_var (m_params m)) v) eqn : Hty; auto.
  simpl. fold pat_constr_vars_inner.
  rewrite IHl0; auto.
Qed.

(*Get strictly smaller (not just <=) vars*)
Fixpoint pat_constr_vars (m: mut_adt) (vs: list vty) (p: pattern) : list vsymbol :=
  match p with
  | Pconstr c tys ps =>
      if constr_in_m c m &&
      list_eq_dec vty_eq_dec tys vs &&
      (length ps =? length (s_args c)) then
      big_union vsymbol_eq_dec (pat_constr_vars_inner m vs)
        (map fst (filter (fun (x: pattern * vty) => 
          vty_in_m m (map vty_var (m_params m)) (snd x)) (combine ps (s_args c))))
      else nil
      (*Only take those where the s_args is in m
        or else we get extra vsymbols which are not necessarily
        smaller (like the head in list)*)
  | Por p1 p2 =>
      intersect vsymbol_eq_dec (pat_constr_vars m vs p1)
        (pat_constr_vars m vs p2)
  (*Don't add variables*)
  | Pbind p y => pat_constr_vars m vs p
  | _ => nil
  end.

(*Both of these are subsets of [pat_fv]*)
Lemma pat_constr_vars_inner_fv (m: mut_adt) (vs: list vty) (p: pattern):
  forall x, In x (pat_constr_vars_inner m vs p) ->
  In x (pat_fv p).
Proof.
  intros x. induction p.
  - simpl; intros.
    destruct (vsym_in_m m vs v). apply H.
    inversion H.
  - rewrite pat_constr_vars_inner_eq.
    intros.
    destruct (constr_in_m f m && list_eq_dec vty_eq_dec vs0 vs &&
    (Datatypes.length ps =? Datatypes.length (s_args f))) eqn : Hconds;
     [|inversion H0].
    bool_hyps.
    apply Nat.eqb_eq in H2.
    simpl_set.
    destruct H0 as [p' [Hinp' Hinx]].
    rewrite in_map_iff in Hinp'.
    destruct Hinp' as [[p'' t'] [Hp' Hint]]; simpl in *; subst.
    rewrite in_filter in Hint.
    destruct Hint as [_ Hincomb].
    rewrite in_combine_iff in Hincomb; auto.
    destruct Hincomb as [i [Hi Heq]].
    specialize (Heq Pwild vty_int); inversion Heq; subst; clear Heq.
    simpl_set. exists (nth i ps Pwild). split; [apply nth_In; auto|].
    rewrite Forall_forall in H. apply H.
    apply nth_In; auto. auto.
  - simpl. auto.
  - simpl. intros.
    rewrite intersect_elts in H.
    destruct H.
    simpl_set. left. apply IHp1; auto.
  - simpl. intros.
    simpl_set. destruct (vsym_in_m m vs v).
    + destruct H as [[Hxv | []] | Hinx]; subst; auto.
    + destruct H as [[] | Hinx]; auto.
Qed.

Lemma pat_constr_vars_subset (m: mut_adt) (vs: list vty) (p: pattern):
  forall x, In x (pat_constr_vars m vs p) ->
  In x (pat_constr_vars_inner m vs p).
Proof.
  intros x. induction p.
  - simpl; intros. destruct H. 
  - (*constr case is super easy - they are equal*) 
    rewrite pat_constr_vars_inner_eq. auto.
  - auto.
  - simpl. rewrite !intersect_elts; intros; destruct_all; split; auto.
  - simpl. intros. rewrite union_elts. auto. 
Qed.

Lemma pat_constr_vars_fv (m: mut_adt) (vs: list vty) (p: pattern):
forall x, In x (pat_constr_vars m vs p) ->
In x (pat_fv p).
Proof.
  intros. apply pat_constr_vars_subset in H.
  apply (pat_constr_vars_inner_fv _ _ _ _ H).
Qed.

End SmallVar.

(*When considering the variable we recurse on, we represent it
  as an option: if we overwrite it (say, with a let binding),
  it is no longer valid to match and recurse on this*)

Definition upd_option (hd: option vsymbol) (x: vsymbol) : option vsymbol :=
  match hd with
  | Some y => if vsymbol_eq_dec x y then None else hd
  | None => None
  end.

Definition upd_option_iter (hd: option vsymbol) (xs: list vsymbol) :
  option vsymbol :=
  fold_right (fun x acc => upd_option acc x) hd xs.

(*Package the function definition components (including
  the index of the decreasing arguments) into a structure*)

Record sn := mk_sn {sn_sym: fpsym; sn_args: list vsymbol;
  sn_idx: nat}.

Definition sn_wf (s: sn): Prop :=
  sn_idx s < length (sn_args s) /\
  length (sn_args s) = length (s_args (sn_sym s)) /\
  NoDup (sn_args s) /\
  map snd (sn_args s) = s_args (sn_sym s).

Record fn := mk_fn {fn_sym: funsym; fn_sn : sn; fn_body: term}.

Coercion fn_sn : fn >-> sn.

Definition fn_wf (f: fn) : Prop :=
  sn_wf f /\
  f_sym (fn_sym f) = sn_sym (fn_sn f).

Record pn := mk_pn {pn_sym: predsym; pn_sn: sn; pn_body: formula}.

Coercion pn_sn : pn >-> sn.

Definition pn_wf (p: pn) : Prop :=
  sn_wf p /\
  p_sym (pn_sym p) = sn_sym (pn_sn p).

(*Decidable equality*)

Definition sn_eqb  (s1 s2: sn) : bool :=
  fpsym_eqb (sn_sym s1) (sn_sym s2) &&
  list_eqb vsymbol_eqb (sn_args s1) (sn_args s2) &&
  (sn_idx s1 =? sn_idx s2).

Definition fn_eqb (f1 f2: fn) : bool :=
  funsym_eqb (fn_sym f1) (fn_sym f2) &&
  sn_eqb (fn_sn f1) (fn_sn f2) &&
  term_eqb (fn_body f1) (fn_body f2).

Definition pn_eqb (p1 p2: pn) : bool :=
  predsym_eqb (pn_sym p1) (pn_sym p2) &&
  sn_eqb (pn_sn p1) (pn_sn p2) &&
  formula_eqb (pn_body p1) (pn_body p2).

Lemma sn_eqb_spec (s1 s2: sn) :
  reflect (s1 = s2) (sn_eqb s1 s2).
Proof.
  unfold sn_eqb.
  dec (fpsym_eqb_spec (sn_sym s1) (sn_sym s2)).
  dec (list_eqb_spec _ vsymbol_eqb_spec (sn_args s1) (sn_args s2)).
  dec (Nat.eqb_spec (sn_idx s1) (sn_idx s2)).
  apply ReflectT.
  destruct s1; destruct s2; simpl in *; subst; auto.
Qed.

Lemma fn_eqb_spec (f1 f2: fn) :
  reflect (f1 = f2) (fn_eqb f1 f2).
Proof.
  unfold fn_eqb.
  dec (funsym_eqb_spec (fn_sym f1) (fn_sym f2)).
  dec (sn_eqb_spec (fn_sn f1) (fn_sn f2)).
  dec (term_eqb_spec (fn_body f1) (fn_body f2)).
  apply ReflectT. destruct f1; destruct f2; simpl in *; subst; auto.
Qed.

Lemma pn_eqb_spec (p1 p2: pn) :
  reflect (p1 = p2) (pn_eqb p1 p2).
Proof.
  unfold pn_eqb.
  dec (predsym_eqb_spec (pn_sym p1) (pn_sym p2)).
  dec (sn_eqb_spec (pn_sn p1) (pn_sn p2)).
  dec (formula_eqb_spec (pn_body p1) (pn_body p2)).
  apply ReflectT. destruct p1; destruct p2; simpl in *; subst; auto.
Qed.

(*Then, we define the termination metric: we require that
  the function is structurally decreasing. The following
  relation describes when a term or formula is decreasing,
  assuming that "small" is a list of vsymbols known to be
  smaller, and "hd" is an option vsymbol that, if Some h,
  means that h is equal to the value we are recursing on*)

Unset Elimination Schemes.
(*list of vsymbols are known to be smaller
  option vsymbol is equal, if it is some
  It is an option because it can be shadowed, say by a let statement*)
(*We have the relation : dec fs ps small hd m vs t ->
  means that 
  1. all ocurrences of functions/pred syms in fs and ps 
    occur where the decreasing argument comes from small,
    which is a list of elements that are smaller than hd
    and which come from the same mut adt as hd*)
Inductive decrease_fun (fs: list fn) (ps: list pn) : 
  list vsymbol -> option vsymbol -> mut_adt -> list vty -> term -> Prop :=
  (*Before any of the constructor cases, if none of fs or ps appear
    in t, then t is trivially a decreasing function*)
  | Dec_notin_t: forall (small: list vsymbol) (hd: option vsymbol) (m: mut_adt)
    (vs: list vty) (t: term),
    (forall (f: fn), In f fs -> negb (funsym_in_tm (fn_sym f) t)) ->
    (forall p, In p ps -> negb (predsym_in_tm (pn_sym p) t)) ->
    decrease_fun fs ps small hd m vs t
  (*First, the recursive function call case*)
  | Dec_fun_in: forall (small: list vsymbol) (hd: option vsymbol) (m: mut_adt)
    (vs: list vty) 
    (f: funsym) (f_decl: fn) (l: list vty) (ts: list term) (x: vsymbol),
    In f_decl fs ->
    f = fn_sym f_decl ->
    (*The decreasing argument is a variable in our list of decreasing terms*)
    In x small ->
    nth (sn_idx f_decl) ts tm_d = Tvar x ->
    (*Uniformity: we must be applying the function uniformly
      (TODO: make this separate?)*)
    l = map vty_var (s_params f) ->
    (*None of [fs] of [ps] appear in the terms*) 
    (*TODO: will likely need this to show we can ignore function binding in interp for recursive cases*)
    Forall (fun t => forall f,  In f fs -> negb (funsym_in_tm (fn_sym f) t)) ts ->
    Forall (fun t => forall p, In p ps -> negb (predsym_in_tm (pn_sym p) t)) ts ->
    (*Then this recursive call is valid*)
    decrease_fun fs ps small hd m vs (Tfun f l ts)
  (*Other function call*)
  | Dec_fun_notin: forall (small: list vsymbol) (hd: option vsymbol)
    (m: mut_adt) (vs: list vty) 
    (f: funsym) (l: list vty) (ts: list term),
    ~ In f (map fn_sym fs) ->
    (*In this case, just recursive*)
    (*TODO: Forall doesn't give ind principle*)
    (forall t, In t ts -> (decrease_fun fs ps small hd m vs t)) ->
    decrease_fun fs ps small hd m vs (Tfun f l ts)
  (*Pattern match on var - this is how we add new, smaller variables*)
  | Dec_tmatch: forall (small: list vsymbol) (hd: option vsymbol) 
    (m: mut_adt)
    (vs: list vty) (a: alg_datatype)
    (mvar: vsymbol) (v: vty) (pats: list (pattern * term)),
    (*TODO: can we only match on a variable?*)
    (hd = Some mvar) \/ In mvar small ->
    adt_in_mut a m ->
    snd mvar = vty_cons (adt_name a) vs ->
    (*TODO: don't allow repeated matches on same variable
      TODO: now we do, makes things easier*)
    (forall (x: pattern * term), In x pats ->
      decrease_fun fs ps 
      (*remove pat_fv's (bound), add back constr vars (smaller)*)
      (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
        small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) ->
    decrease_fun fs ps small hd m vs (Tmatch (Tvar mvar) v pats) 
  (*Other pattern match is recursive case*)
  | Dec_tmatch_rec: forall (small: list vsymbol) (hd: option vsymbol)
    m vs
    (tm: term) (v: vty) (pats: list (pattern * term)),
    ~(exists var, tm = Tvar var /\ (hd = Some var \/ In var small)) ->
    decrease_fun fs ps small hd m vs tm ->
    (forall x, In x pats ->
      decrease_fun fs ps 
      (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) ->
    decrease_fun fs ps small hd m vs (Tmatch tm v pats)
  (*Now the easy cases: Constants, Variables always decreasing*)
  | Dec_var: forall (small : list vsymbol) (hd: option vsymbol) m vs (v: vsymbol),
    decrease_fun fs ps small hd m vs (Tvar v)
  | Dec_const: forall (small : list vsymbol) (hd: option vsymbol) m vs (c: constant),
    decrease_fun fs ps small hd m vs (Tconst c)
  (*Recursive cases: let, if, eps*)
  | Dec_tlet: forall (small: list vsymbol) (hd: option vsymbol) m vs (t1: term)
    (v: vsymbol) (t2: term),
    decrease_fun fs ps small hd m vs t1 ->
    (*v is bound, so it is no longer smaller in t2 or equal in hd*)
    decrease_fun fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) m vs t2 ->
    decrease_fun fs ps small hd m vs (Tlet t1 v t2)
  | Dec_tif: forall (small: list vsymbol) (hd: option vsymbol) m vs (f1: formula)
    (t1 t2: term),
    decrease_pred fs ps small hd m vs f1 ->
    decrease_fun fs ps small hd m vs t1 ->
    decrease_fun fs ps small hd m vs t2 ->
    decrease_fun fs ps small hd m vs (Tif f1 t1 t2)
  | Dec_eps: forall (small: list vsymbol) (hd: option vsymbol) m vs (f: formula)
    (v: vsymbol),
    decrease_pred fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f ->
    decrease_fun fs ps small hd m vs (Teps f v)
(*This is very similar*)
with decrease_pred (fs: list fn) (ps: list pn) : 
  list vsymbol -> option vsymbol -> mut_adt -> list vty -> formula -> Prop :=
  | Dec_notin_f: forall (small: list vsymbol) (hd: option vsymbol) (m: mut_adt)
  (vs: list vty) (fmla: formula),
  (forall f, In f fs -> negb (funsym_in_fmla (fn_sym f) fmla)) ->
  (forall p, In p ps -> negb (predsym_in_fmla (pn_sym p) fmla)) ->
  decrease_pred fs ps small hd m vs fmla
  (*First, the recursive predicate call case*)
  | Dec_pred_in: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (p: predsym) (p_decl: pn) (l: list vty) (ts: list term) x,
    In p_decl ps ->
    p = pn_sym p_decl ->
    (*The decreasing argument must be in our list of decreasing terms*)
    In x small ->
    nth (sn_idx p_decl) ts tm_d = Tvar x ->
    (*Uniformity: we must be applying the function uniformly
    (TODO: make this separate?)*)
    l = map vty_var (s_params p) ->
    (*None of [fs] or[ps] appear in the terms*) 
    Forall (fun t => forall f,  In f fs -> negb (funsym_in_tm (fn_sym f) t)) ts ->
    Forall (fun t => forall p, In p ps -> negb (predsym_in_tm (pn_sym p) t)) ts ->
    (*Then this recursive call is valid*)
    decrease_pred fs ps small hd m vs (Fpred p l ts)
  (*Other predicate call*)
  | Dec_pred_notin: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (p: predsym) (l: list vty) (ts: list term),
    ~ In p (map pn_sym ps) ->
    (*In this case, just recursive*)
    (forall t, In t ts -> decrease_fun fs ps small hd m vs t) ->
    decrease_pred fs ps small hd m vs (Fpred p l ts)
  (*Pattern match on var - this is how we add new, smaller variables*)
  | Dec_fmatch: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (a: alg_datatype)
    (mvar: vsymbol) (v: vty) (pats: list (pattern * formula)),
    (*TODO: can we only match on a variable?*)
    hd = Some mvar \/ In mvar small ->
    adt_in_mut a m ->
    snd mvar = vty_cons (adt_name a) vs ->
    (*TODO: don't allow repeated matches on same variable*)
    (forall x, In x pats -> decrease_pred fs ps 
      (*remove pat_fv's (bound), add back constr vars (smaller)*)
      (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
        small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) ->
    decrease_pred fs ps small hd m vs (Fmatch (Tvar mvar) v pats)
  (*Other pattern match is recursive case*)
  | Dec_fmatch_rec: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (tm: term) (v: vty) (pats: list (pattern * formula)),
    ~(exists var, tm = Tvar var /\ (hd = Some var \/ In var small)) ->
    decrease_fun fs ps small hd m vs tm ->
    (forall x, In x pats ->
      decrease_pred fs ps 
      (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) ->
    decrease_pred fs ps small hd m vs (Fmatch tm v pats)
  (*Easy cases: true, false*)
  | Dec_true: forall (small: list vsymbol) (hd: option vsymbol) m vs,
    decrease_pred fs ps small hd m vs Ftrue
  | Dec_false: forall (small: list vsymbol) (hd: option vsymbol) m vs,
    decrease_pred fs ps small hd m vs Ffalse
  (*Recursive cases: not, quantifier, eq, binop, let, if*)
  | Dec_not: forall small hd m vs f,
    decrease_pred fs ps small hd m vs f ->
    decrease_pred fs ps small hd m vs (Fnot f)
  | Dec_quant: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (q: quant) (v: vsymbol) (f: formula),
    decrease_pred fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f ->
    decrease_pred fs ps small hd m vs (Fquant q v f)
  | Dec_eq: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (ty: vty) (t1 t2: term),
    decrease_fun fs ps small hd m vs t1 ->
    decrease_fun fs ps small hd m vs t2 ->
    decrease_pred fs ps small hd m vs (Feq ty t1 t2)
  | Dec_binop: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (b: binop) (f1 f2: formula),
    decrease_pred fs ps small hd m vs f1 ->
    decrease_pred fs ps small hd m vs f2 ->
    decrease_pred fs ps small hd m vs (Fbinop b f1 f2)
  | Dec_flet: forall (small: list vsymbol) (hd: option vsymbol) m vs (t1: term)
    (v: vsymbol) (f: formula),
    decrease_fun fs ps small hd m vs t1 ->
    decrease_pred fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f ->
    decrease_pred fs ps small hd m vs (Flet t1 v f)
  | Dec_fif: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (f1 f2 f3: formula),
    decrease_pred fs ps small hd m vs f1 ->
    decrease_pred fs ps small hd m vs f2 ->
    decrease_pred fs ps small hd m vs f3 ->
    decrease_pred fs ps small hd m vs (Fif f1 f2 f3)
    .
Set Elimination Schemes.
Scheme decrease_fun_ind := Minimality for decrease_fun Sort Prop
with decrease_pred_ind := Minimality for decrease_pred Sort Prop.

(*Now we define how to convert a [funpred_def] to an fs or ps, given 
  an index*)

Definition fundef_to_fn (f: funsym) (vars: list vsymbol) (t: term)
  (i: nat): fn :=
  mk_fn f (mk_sn (f_sym f) vars i) t.

Lemma fundef_fn_wf (f: funsym) (vars: list vsymbol) (t: term)
  (i: nat) (Hi: i < length (s_args f)) (Hn: NoDup vars)
  (Hargs: map snd vars = s_args f) :
  fn_wf (fundef_to_fn f vars t i).
Proof.
  assert (length vars = length (s_args f)) by
    (rewrite <- Hargs, map_length; auto).
  unfold fn_wf. split; auto.
  unfold sn_wf. repeat (split; auto).
  simpl. lia.
Qed.

Definition preddef_to_pn (p: predsym) (vars: list vsymbol) (f: formula)
  (i: nat) : pn :=
  mk_pn p (mk_sn (p_sym p) vars i) f.

Lemma preddef_pn_wf (p: predsym) (vars: list vsymbol) (f: formula)
  (i: nat) (Hi: i < length (s_args p)) (Hn: NoDup vars) 
  (Hargs: map snd vars = s_args p) : 
  pn_wf (preddef_to_pn p vars f i).
Proof.
  assert (length vars = length (s_args p)) by
    (rewrite <- Hargs, map_length; auto).
  unfold pn_wf. split; auto.
  unfold sn_wf. split; auto.
  simpl; lia.
Qed.

(*We need a default [funpred_def]*)
(*TODO: shouldn't use id*)
Definition fd_d : funpred_def :=
  fun_def id_fs nil tm_d.

(*We need to do 2 passes: first, check that each individual
  component is well-typed and well-formed, then do the termination
  checking*)

(*First, individual checking*)

(*A function/pred symbol is well-typed if the term has the correct return type of
  the function and all free variables in t are included in the arguments vars*)
Definition funpred_def_valid_type (fd: funpred_def) : Prop :=
  match fd with
  | fun_def f vars t =>
    term_has_type gamma t (f_ret f) /\
    sublist (tm_fv t) vars /\
    sublist (tm_type_vars t) (s_params f) /\
    NoDup (map fst vars) /\
    map snd vars = s_args f (*types of args correct*)
  | pred_def p vars f =>
    valid_formula gamma f /\
    sublist (fmla_fv f) vars /\
    sublist (fmla_type_vars f) (s_params p) /\
    NoDup (map fst vars) /\
    map snd vars = s_args p (*types of args correct*)
  end.

(*Now we deal with termination. We need the following:
  There is a list is of nats such that
  1. length is = length l (number of mut. rec. functions)
  2. For all n, n < length is -> nth n is < length (s_args nth n l)
    (all i's are bounded)
  3. There is a mutually recursive type m and arguments vs of 
    correct length such that if we build the fn and pn instances 
    for each l using i as the value, each function body satisfies
    [decrease_fun] or [decrease_pred]
  
  Finally, we need all type parameters for the function to be
  equal (say, equal to some list params)
  *)

(*It will be more convenient to have our list as follows:
  all fundefs, followed by all preddefs*)

Definition split_funpred_defs (l: list funpred_def):
  list (funsym * list vsymbol * term) *
  list (predsym * list vsymbol * formula) :=
  (fold_right (fun x acc =>
    let tl := acc in
    match x with
    | fun_def f vs t => ((f, vs, t) :: fst tl, snd tl)
    | pred_def p vs f => (fst tl, (p, vs, f) :: snd tl)
    end) (nil, nil) l).

Lemma split_funpred_defs_length l :
  length (fst (split_funpred_defs l)) +
  length (snd (split_funpred_defs l)) = length l.
Proof.
  induction l; simpl; auto; destruct a; simpl; lia.
Qed.

(*Create list of fs and ps*)
Definition funpred_defs_to_sns (l: list funpred_def) (li: list nat)
: (list fn * list pn) :=
let t := split_funpred_defs l in
(map (fun x =>
  fundef_to_fn (fst (fst (fst x))) (snd (fst (fst x))) (snd (fst x)) (snd x))
  (combine (fst t) (firstn (length (fst t)) li)),
map (fun x =>
  preddef_to_pn (fst (fst (fst x))) (snd (fst (fst x))) (snd (fst x)) (snd x))
  (combine (snd t) (skipn (length (fst t)) li))
).

Lemma funpred_defs_to_sns_length l is:
  length l = length is ->
  length (fst (funpred_defs_to_sns l is)) +
  length (snd (funpred_defs_to_sns l is)) = length l.
Proof.
  intros. unfold funpred_defs_to_sns.
  simpl. rewrite !map_length, !combine_length, !firstn_length, 
  !skipn_length.
  pose proof (split_funpred_defs_length l). lia.
Qed.

Lemma map_fst_fst_fst_combine: forall {A B C D: Type} l1 l2,
  length l1 = length l2 ->
  map (fun (x : A * B * C * D) => fst (fst (fst x)))
    (combine l1 l2) =
  map (fun (x: A * B * C) => fst (fst x)) l1. 
  intros. generalize dependent l2. induction l1; simpl; intros; auto;
  destruct l2; simpl; auto; inversion H. rewrite IHl1; auto.
Qed.

Definition sn_d : sn :=
  (mk_sn id_sym [vs_d] 0).

(*TODO: just use ssreflect?*)
Lemma firstn_nth {A: Type} (n: nat) (l: list A) (i: nat) (x: A):
  i < n ->
  nth i (firstn n l) x = nth i l x.
Proof.
  revert i l. induction n; simpl; intros; try lia.
  destruct l; auto; simpl.
  destruct i; auto. apply (IHn i l (ltac:(lia))).
Qed.

Lemma skipn_nth {A: Type} (n: nat) (l: list A) (i: nat) (x: A):
  nth i (skipn n l) x = nth (n + i) l x.
Proof.
  revert i l. induction n; simpl; intros; auto.
  destruct l; auto; simpl;
  destruct i; auto.
Qed.

(*Specs for [funpred_defs_to_sns]*)
Lemma funpred_defs_to_sns_in_fst (l: list funpred_def) (is: list nat) (x: fn):
  length l = length is ->
  In x (fst (funpred_defs_to_sns l is)) <->
  exists i,
    i < length (fst (split_funpred_defs l)) /\
    let y := (nth i (fst (split_funpred_defs l)) (id_fs, nil, tm_d)) in 
    x = fundef_to_fn (fst (fst y)) (snd (fst y)) (snd y)
    (nth i is 0).
Proof. 
  intros Hlen.
  pose proof (split_funpred_defs_length l) as Hlen'.
  unfold funpred_defs_to_sns; simpl.
  rewrite in_map_iff. split; intros.
  - destruct H as [y [Hx Hiny]]; subst.
    rewrite in_combine_iff in Hiny.
    destruct Hiny as [i [Hi Hy]].
    exists i. split; auto.
    specialize (Hy (id_fs, nil, tm_d) 0). subst. simpl. f_equal.
    (*Ugh, need firstn nth*)
    rewrite firstn_nth; auto.
    rewrite firstn_length, <- Hlen. lia.
  - destruct H as [i [Hi Hx]]. subst.
    exists (nth i (fst (split_funpred_defs l)) (id_fs, nil, tm_d), nth i is 0).
    split; auto.
    rewrite in_combine_iff. exists i.
    split; auto. intros.
    rewrite firstn_nth; auto.
    (*need nth firstn again*)
    f_equal; apply nth_indep; auto.
    rewrite <- Hlen. lia.
    rewrite firstn_length, <- Hlen. lia.
Qed.

(*This is not great*)
Definition id_ps : predsym :=
  Build_predsym id_sym.

Lemma funpred_defs_to_sns_in_snd (l: list funpred_def) (is: list nat) 
  (x: pn):
  length l = length is ->
  In x (snd (funpred_defs_to_sns l is)) <->
  exists i,
    i < length (snd (split_funpred_defs l)) /\
    let y := (nth i (snd (split_funpred_defs l)) (id_ps, nil, Ftrue)) in 
    x = preddef_to_pn (fst (fst y)) (snd (fst y)) (snd y)
    (nth ((length (fst (funpred_defs_to_sns l is))) + i) is 0).
Proof. 
  intros Hlen.
  pose proof (split_funpred_defs_length l) as Hlen'.
  unfold funpred_defs_to_sns; simpl.
  rewrite in_map_iff. split; intros.
  - destruct H as [y [Hx Hiny]]; subst.
    rewrite in_combine_iff in Hiny.
    destruct Hiny as [i [Hi Hy]].
    exists i. split; auto.
    specialize (Hy (id_ps, nil, Ftrue) 0). subst. simpl. f_equal.
    rewrite map_length, combine_length.
    + rewrite skipn_nth. f_equal. f_equal.
      rewrite firstn_length. lia.
    + rewrite skipn_length. lia.
  - destruct H as [i [Hi Hx]]. subst.
    exists (nth i (snd (split_funpred_defs l)) (id_ps, nil, Ftrue), 
      nth (length (fst (split_funpred_defs l)) + i) is 0).
    split; simpl; auto.
    + f_equal. rewrite map_length, combine_length, firstn_length.
      f_equal. lia.
    + rewrite in_combine_iff. exists i.
      split; auto. intros.
      rewrite skipn_nth; auto.
      (*need nth firstn again*)
      f_equal; apply nth_indep; auto. lia.
      rewrite skipn_length, <- Hlen. lia.
Qed.

Lemma split_funpred_defs_in_l (l: list funpred_def):
  (forall x, In x (fst (split_funpred_defs l)) <->
    In (fun_def (fst (fst x)) (snd (fst x)) (snd x)) l) /\
  (forall x, In x (snd (split_funpred_defs l)) <->
    In (pred_def (fst (fst x)) (snd (fst x)) (snd x)) l).
Proof.
  induction l; simpl; split; intros; try reflexivity.
  - destruct a; simpl; split; intros; destruct_all; auto;
    try solve[right; apply H0; auto]; try solve[apply H0; auto];
    try discriminate.
    inversion H; subst. left. destruct x. destruct p. reflexivity.
  - destruct a; simpl; split; intros; destruct_all; auto;
    try solve[right; apply H1; auto]; try solve[apply H1; auto];
    try discriminate.
    inversion H; subst. left. destruct x. destruct p. reflexivity.
Qed.

Lemma funpred_def_to_sns_wf (l: list funpred_def) (is: list nat)
  (Hlen: length is = length l)
  (Hall: forall i, i < length is -> 
    nth i is 0 < length (s_args (nth i 
      (map (fun x => f_sym (fst (fst x))) (fst (split_funpred_defs l)) ++
       map (fun x => p_sym (fst (fst x))) (snd (split_funpred_defs l)))
      id_fs)))
  (Hl: Forall funpred_def_valid_type l):
  Forall fn_wf (fst (funpred_defs_to_sns l is)) /\
  Forall pn_wf (snd (funpred_defs_to_sns l is)).
Proof.
  pose proof (split_funpred_defs_length l) as Hlen'.
  split.
  - rewrite Forall_forall.
    intros f.
    rewrite Forall_forall in Hl.
    rewrite funpred_defs_to_sns_in_fst; auto.
    intros [i [Hi Hf]]. rewrite Hf.
    set (y:=nth i (fst (split_funpred_defs l)) (id_fs, [], tm_d)) in *.
    simpl in Hf. 
    assert (Hinl: In (fun_def (fst (fst y)) (snd (fst y)) (snd y)) l). {
      apply split_funpred_defs_in_l. subst y. apply nth_In. auto.
    }
    specialize (Hl _ Hinl). simpl in Hl.
    destruct_all.
    apply fundef_fn_wf; auto.
    + specialize (Hall i ltac:(lia)).
      revert Hall. rewrite app_nth1 by (rewrite map_length; auto).
      rewrite map_nth_inbound with (d2:=(id_fs, nil, tm_d)); auto.
    + apply NoDup_map_inv in H2; auto.
  - (*Very similar*)
    rewrite Forall_forall.
    intros p.
    rewrite Forall_forall in Hl.
    rewrite funpred_defs_to_sns_in_snd; auto.
    intros [i [Hi Hp]]. rewrite Hp.
    set (y:= nth i (snd (split_funpred_defs l)) (id_ps, [], Ftrue)) in *.
    simpl in Hp.
    assert (Hinl: In (pred_def (fst (fst y)) (snd (fst y)) (snd y)) l). {
      apply split_funpred_defs_in_l. subst y. apply nth_In. auto.
    }
    specialize (Hl _ Hinl). simpl in Hl.
    destruct_all.
    apply preddef_pn_wf; auto.
    + specialize (Hall (length (fst (split_funpred_defs l)) + i) ltac:(lia)).
      revert Hall. rewrite app_nth2 by (rewrite map_length; lia).
      rewrite map_length.
      replace (length (fst (split_funpred_defs l)) + i -
        length (fst (split_funpred_defs l))) with i by lia.
      rewrite map_nth_inbound with (d2:=(id_ps, nil, Ftrue)); auto.
      subst y; simpl. rewrite map_length.
      replace (length (combine (fst (split_funpred_defs l))
      (firstn (Datatypes.length (fst (split_funpred_defs l))) is)))
      with (length (fst (split_funpred_defs l))); auto.
      rewrite combine_length, firstn_length. lia.
    + apply (NoDup_map_inv) in H2. auto.
Qed.

(*TODO: name (term is termination)*)
(*The condition for termination*)
Definition funpred_def_term (l: list funpred_def)
  (m: mut_adt) (params: list typevar) (vs: list vty)
    (is: list nat) :=
    l <> nil /\
    let fs := fst (funpred_defs_to_sns l is) in
    let ps := snd (funpred_defs_to_sns l is) in
    length vs = length (m_params m) /\
    mut_in_ctx m gamma /\
    length is = length l /\
    (forall i, i < length is -> 
    (*The ith element in is should give s_args of the ith elt
      in the combined list*)
    nth i is 0 < length (s_args (nth i 
      (map (fun x => f_sym (fst (fst x))) (fst (split_funpred_defs l)) ++
      map (fun x => p_sym (fst (fst x))) (snd (split_funpred_defs l)))
    id_fs))) /\
    (*All functions recurse on ADT instance*)
    (forall f, In f fs -> 
      vty_in_m m vs (snd (nth (sn_idx f) (sn_args f) vs_d))) /\
    (forall p, In p ps ->
      vty_in_m m vs (snd (nth (sn_idx p) (sn_args p) vs_d))) /\
    (*All functions have params = params*)
    (forall f, In f fs -> s_params (fn_sym f) = params) /\
    (forall p, In p ps -> s_params (pn_sym p) = params) /\
    (*All functions are structurally (mutually) decreasing
    on mut type m(vs)*)
    Forall (fun (f: fn) => decrease_fun fs ps nil 
      (Some (nth (sn_idx f) (sn_args f) vs_d)) m vs (fn_body f)) fs /\
    Forall (fun (p: pn) => decrease_pred fs ps nil 
      (Some (nth (sn_idx p) (sn_args p) vs_d)) m vs (pn_body p)) ps.

Definition funpred_def_term_exists (l: list funpred_def) :=
  exists (m: mut_adt) (params: list typevar) (vs: list vty)
  (is: list nat),
  funpred_def_term l m params vs is.

(*Now, the final requirement for a well-typed mutually
  recursive function definition: combine these*)

Definition funpred_valid (l: list funpred_def) :=
    ((Forall funpred_def_valid_type l) /\
    funpred_def_term_exists l).

End RecFun.
(*Inductive Predicates*)
Section IndProp.

(*Each clause must be a closed formula, well-typed, and belong to a restricted grammar, which
  we give both as an inductive definition and a computable Fixpoint below*)

Inductive valid_ind_form (p: predsym) : formula -> Prop :=
  | VI_pred: forall (tys : list vty) tms,
    tys = map vty_var (s_params p) ->
    length (s_args p) = length tms ->
    valid_ind_form p (Fpred p tys tms)
  | VI_impl: forall f1 f2,
    valid_ind_form p f2 ->
    valid_ind_form p (Fbinop Timplies f1 f2)
  | VI_forall: forall x f,
    valid_ind_form p f ->
    valid_ind_form p (Fquant Tforall x f)
  | VI_let: forall x t f,
    valid_ind_form p f ->
    valid_ind_form p (Flet t x f).
     
Fixpoint valid_ind_form_dec (p: predsym) (f: formula) : bool :=
  match f with
  | Fpred p' tys tms => predsym_eq_dec p p' && list_eq_dec vty_eq_dec tys (map vty_var (s_params p))
    && (length (s_args p) =? length tms)
  | Fquant Tforall x f' => valid_ind_form_dec p f'
  | Fbinop Timplies f1 f2 => valid_ind_form_dec p f2
  | Flet t x f' => valid_ind_form_dec p f'
  | _ => false
  end.

Lemma valid_ind_form_equiv: forall p f,
  reflect (valid_ind_form p f) (valid_ind_form_dec p f).
Proof.
  intros. apply iff_reflect. 
  induction f using formula_ind with (P1:=(fun _ => True)); auto; simpl;
  (split; [intros C;inversion C; subst| intros]); auto; try solve[intuition]; try solve[constructor];
  try match goal with | H: false = true |- _ => inversion H end.
  - rewrite H4, Nat.eqb_refl, andb_true_r. apply andb_true_intro; split; simpl_sumbool. 
  - repeat(apply andb_prop in H0; destruct H0). repeat simpl_sumbool. constructor; auto.
    apply Nat.eqb_eq. auto.
  - destruct q;[constructor; intuition |inversion H].
  - destruct b; try inversion H. constructor. intuition.
  - constructor. intuition.
Qed.

Definition indprop_valid_type (i: indpred_def) : Prop :=
  match i with
  | ind_def p lf => Forall (fun f => 
    (*each formula is well-typed*)
    valid_formula gamma f /\
    (*and closed (no free vars)*) 
    closed_formula f /\ 
    (*And has the correct form for an inductive predicate*)
    valid_ind_form p f /\
    (*And all type variables appearing in the formula appear
      in the parameters of p*)
    sublist (fmla_type_vars f) (s_params p)) 
    (map snd lf)
  end.

(*Strict Positivity*)

(*Here, strict positivity is a bit simpler, because predicates are not
  higher-order; we only need to reason about implication, essentially *)

(*Inductive case and nested positivity cannot occur because we cannot
  take a predicate as an argument (ie: can't have list x, where x : Prop)*)
Inductive ind_strictly_positive (ps: list predsym) : formula -> Prop :=
  | ISP_notin: forall (f: formula),
    (forall p, In p ps -> negb (predsym_in_fmla p f)) ->
    ind_strictly_positive ps f
  | ISP_pred: forall (p: predsym) 
    (vs: list vty) (ts: list term),
    In p ps ->
    (forall x t, In t ts -> In x ps -> negb (predsym_in_tm x t)) ->
    ind_strictly_positive ps (Fpred p vs ts)
  | ISP_impl: forall  (f1 f2: formula),
    ind_strictly_positive ps f2 ->
    (forall p, In p ps -> negb(predsym_in_fmla p f1)) ->
    ind_strictly_positive ps (Fbinop Timplies f1 f2)
  (*The rest of the cases are not too interesting*)
  | ISP_quant: forall (q: quant) (x: vsymbol) (f: formula),
    ind_strictly_positive ps f ->
    ind_strictly_positive ps (Fquant q x f)
  | ISP_and: forall (f1 f2 : formula),
    ind_strictly_positive ps f1 ->
    ind_strictly_positive ps f2 ->
    ind_strictly_positive ps (Fbinop Tand f1 f2)
  | ISP_or: forall (f1 f2 : formula),
    ind_strictly_positive ps f1 ->
    ind_strictly_positive ps f2 ->
    ind_strictly_positive ps (Fbinop Tor f1 f2)
  | ISP_let: forall (t: term) (x: vsymbol) (f: formula),
    (forall p, In p ps -> negb (predsym_in_tm p t)) ->
    ind_strictly_positive ps f -> (*TODO: is this too restrictive as well? Think OK*)
    ind_strictly_positive ps (Flet t x f)
  | ISP_if: forall f1 f2 f3,
    (*Cannot be in guard because get (essentially), f1 -> f2 /\ ~f1 -> f3*)
    (forall p, In p ps -> negb(predsym_in_fmla p f1)) ->
    ind_strictly_positive ps f2 ->
    ind_strictly_positive ps f3 ->
    ind_strictly_positive ps (Fif f1 f2 f3)
  | ISP_match: forall (t: term) ty (pats: list (pattern * formula)),
    (forall p, In p ps -> negb (predsym_in_tm p t)) ->
    (forall f, In f (map snd pats) -> ind_strictly_positive ps f) ->
    ind_strictly_positive ps (Fmatch t ty pats) 
  (*eq, not, iff covered by case "notin" - these cannot have even strictly
    positive occurrences *).


Inductive ind_positive (ps: list predsym) : formula -> Prop :=
  | IP_pred: forall (p: predsym) 
    (vs: list vty) (ts: list term),
    In p ps ->
    (forall x t, In t ts -> In x ps -> negb (predsym_in_tm x t)) ->
    ind_positive ps (Fpred p vs ts)
  | IP_forall: forall (x: vsymbol) (f: formula),
    ind_positive ps f ->
    (* Don't need strict positivity for ty because we cannot quantify over formulas*)
    ind_positive ps (Fquant Tforall x f)
  | IP_let: forall (t: term) (x: vsymbol) (f: formula),
    (*TODO: is this the right condition? I think so, but should we allow this
      symbol to appear in terms in any cases?*)
    (forall p, In p ps -> negb (predsym_in_tm p t)) ->
    ind_positive ps f ->
    ind_positive ps (Flet t x f)
  | IP_impl: forall (f1 f2: formula),
    ind_strictly_positive ps f1 ->
    ind_positive ps f2 ->
    ind_positive ps (Fbinop Timplies f1 f2).

Definition indpred_positive (l: list indpred_def) : Prop :=
  let ps : list predsym :=
    map (fun i => match i with |ind_def p fs => p end) l in
  let fs: list formula :=
    concat (map (fun i => match i with |ind_def p fs => map snd fs end) l) in
  Forall (ind_positive ps) fs.

(*For a mutually inductive proposition, all must have
  the same parameters*)

Inductive Forall_eq {A B: Type} (f: A -> B): list A -> Prop :=
  | Forall_eq_nil:
    Forall_eq f nil
  | Forall_eq_cons: forall hd tl,
    Forall_eq f tl ->
    Forall (fun x => f x = f hd) tl ->
    Forall_eq f (hd :: tl).

Lemma Forall_eq_iff {A B: Type} (f: A -> B) (l: list A):
  Forall_eq f l <-> (forall x y, In x l -> In y l -> f x = f y).
Proof.
  induction l; simpl; intros; split; intros; auto. destruct H0.
  constructor.
  - inversion H; subst.
    rewrite Forall_forall in H5.
    destruct H0; destruct H1; subst; auto.
    + symmetry. apply H5; auto.
    + apply IHl; auto.
  - constructor.
    + apply IHl. intros. apply H; auto.
    + rewrite Forall_forall; intros.
      apply H; auto.
Qed.

Definition indpred_params_same (l: list indpred_def) : Prop :=
  Forall_eq (fun i => match i with |ind_def p fs => s_params p end) l.

(*Finally, all recursive instances must be uniform*)

Fixpoint pred_with_params_fmla (ps: list predsym) (params: list typevar)
  (f: formula) {struct f} : bool :=
  match f with
  | Fpred p tys tms =>
    (implb (in_bool predsym_eq_dec p ps) 
      (list_eq_dec vty_eq_dec tys (map vty_var params))) &&
    forallb (pred_with_params_tm ps params) tms
  (*Other cases are not interesting*)
  | Fquant q v f =>
    pred_with_params_fmla ps params f
  | Feq ty t1 t2 =>
    pred_with_params_tm ps params t1 &&
    pred_with_params_tm ps params t2
  | Fbinop b f1 f2 =>
    pred_with_params_fmla ps params f1 &&
    pred_with_params_fmla ps params f2
  | Fnot f =>
    pred_with_params_fmla ps params f
  | Ftrue => true
  | Ffalse => true
  | Flet t v f =>
    pred_with_params_tm ps params t &&
    pred_with_params_fmla ps params f
  | Fif f1 f2 f3 =>
    pred_with_params_fmla ps params f1 &&
    pred_with_params_fmla ps params f2 &&
    pred_with_params_fmla ps params f3
  | Fmatch t v pats =>
    pred_with_params_tm ps params t &&
    forallb id (map (fun x =>
      pred_with_params_fmla ps params (snd x)) pats)
  end
(*No interesting cases, all recursive*)
with pred_with_params_tm (ps: list predsym) (params: list typevar)
  (t: term) {struct t} : bool :=
  match t with
  | Tvar v => true
  | Tconst c => true
  | Tfun _ _ tms => forallb (pred_with_params_tm ps params) tms
  | Tlet t1 v t2 =>
    pred_with_params_tm ps params t1 &&
    pred_with_params_tm ps params t2
  | Tif f t1 t2 =>
    pred_with_params_fmla ps params f &&
    pred_with_params_tm ps params t1 &&
    pred_with_params_tm ps params t2
  | Tmatch t v pats =>
    pred_with_params_tm ps params t &&
    forallb id (map (fun x =>
      pred_with_params_tm ps params (snd x)) pats)
  | Teps f v =>
    pred_with_params_fmla ps params f
  end.

Definition indpred_uniform (ps: list predsym) (fs: list formula) : bool :=
  match ps with
  | nil => true
  | p :: tl => 
    let params := s_params p in
    forallb (fun f => pred_with_params_fmla ps params f) fs
  end.

Definition indpred_def_constrs (i: indpred_def): list formula :=
  match i with
  | ind_def _ fs => map snd fs
  end.

Definition indpreds_uniform (l: list indpred_def) : bool :=
  let ps := predsyms_of_indprop l in
  let fs := concat (map indpred_def_constrs l) in
  indpred_uniform ps fs.

End IndProp.

(*Our validity condition for indprops*)
Definition indprop_valid (is: list indpred_def) : Prop :=
  Forall indprop_valid_type is /\
  indpred_positive is /\
  indpred_params_same is /\
  indpreds_uniform is.

End RecursiveDefs.

Definition valid_def gamma (d: def) : Prop :=
  match d with
  | datatype_def m => mut_valid gamma m
  | inductive_def l => indprop_valid gamma l
  | recursive_def fs => funpred_valid gamma fs
  | _ => True
  end.

Definition nonempty_def (d: def) : bool :=
  match d with
  | datatype_def m => negb (null (typs m))
  | inductive_def l => negb (null l)
  | recursive_def fs => negb (null fs)
  | _ => true
  end.

(*We define a valid context inductively. It consists of 2 parts
  1. The context is well-formed, or all funs/preds are well-formed
    and no type, function, or pred symbols are duplicated or empty
  2. Every concrete definition is valid according to its specific
    checks defined above
  We define this inductively since each definition can only
    rely on the previous ones.
  *)

Inductive valid_context : context -> Prop :=
  | valid_ctx_nil: valid_context nil
  | valid_ctx_cons: forall d gamma,
    valid_context gamma ->
    (*Well-formed symbols*)
    Forall (wf_funsym (d :: gamma)) (funsyms_of_def d) ->
    Forall (wf_predsym (d :: gamma)) (predsyms_of_def d) ->
    (*uniqueness*)
    Forall (fun f => ~ In f (sig_f gamma)) (funsyms_of_def d) ->
    Forall (fun f => ~ In f (sig_p gamma)) (predsyms_of_def d) ->
    Forall (fun ts => ~ In ts (sig_t gamma)) (typesyms_of_def d) ->
    NoDup (funsyms_of_def d) ->
    NoDup (predsyms_of_def d) ->
    NoDup (typesyms_of_def d) ->
    (*nonempty*)
    nonempty_def d ->
    (*checks for concrete defs*)
    valid_def (d :: gamma) d ->
    valid_context (d :: gamma).

(*At some points, we need a weaker notion; only that the
  context is well-formed. We give it here*)

Inductive wf_context : context -> Prop :=
| wf_ctx_nil: wf_context nil
| wf_ctx_mut: forall d gamma,
  wf_context gamma ->
  Forall (wf_funsym (d :: gamma)) (funsyms_of_def d) ->
  Forall (wf_predsym (d :: gamma)) (predsyms_of_def d) ->
  Forall (fun f => ~ In f (sig_f gamma)) (funsyms_of_def d) ->
  Forall (fun f => ~ In f (sig_p gamma)) (predsyms_of_def d) ->
  Forall (fun ts => ~ In ts (sig_t gamma)) (typesyms_of_def d) ->
  NoDup (funsyms_of_def d) ->
  NoDup (predsyms_of_def d) ->
  NoDup (typesyms_of_def d) ->
  wf_context (d:: gamma).

Lemma valid_context_wf gamma:
  valid_context gamma ->
  wf_context gamma.
Proof.
  intros Hval. induction Hval; constructor; auto.
Qed.

(*We need to know that all parts of a context
  remain well-typed and valid if the context is expanded.
  This requires lots of lemmas, though really only the typing
  one is somewhat interesting.*)
Section Expand.

Lemma valid_type_expand gamma d t:
  valid_type gamma t ->
  valid_type (d :: gamma) t.
Proof.
  intros. induction H; try constructor; auto.
  unfold sig_t in *.
  simpl. rewrite in_app_iff. auto.
Qed.

Lemma wf_funsym_expand gamma d f:
  wf_funsym gamma f ->
  wf_funsym (d :: gamma) f.
Proof.
  unfold wf_funsym; apply Forall_impl.
  intros; destruct_all; split; auto;
  apply valid_type_expand; auto.
Qed.

Lemma wf_predsym_expand gamma d p:
  wf_predsym gamma p ->
  wf_predsym (d :: gamma) p.
Proof.
  unfold wf_predsym; apply Forall_impl.
  intros; destruct_all; split; auto;
  apply valid_type_expand; auto.
Qed.

Lemma strictly_positive_expand d gamma t ts:
  strictly_positive gamma t ts ->
  strictly_positive (d :: gamma) t ts.
Proof.
  revert t ts.
  apply (strictly_positive_ind gamma
    (fun v l => strictly_positive (d :: gamma) v l)
    (fun f vs tys ts syms =>
      nested_positive (d :: gamma) f vs tys ts syms)); intros.
  - apply Strict_notin. auto.
  - apply Strict_constr. auto.
  - eapply Strict_ind. 2: apply H0. 2: apply H1. 2: apply H3.
    unfold mut_typs_in_ctx in *.
    destruct H as [vars [H Hin]].
    exists vars. exists H. simpl; auto.
  - constructor; auto.
Qed.

Lemma adt_positive_expand d gamma fs ts:
  positive gamma fs ts ->
  positive (d :: gamma) fs ts.
Proof.
  intros Hpos. induction Hpos.
  constructor; auto.
  intros. apply strictly_positive_expand; auto.
Qed.

Lemma mut_valid_expand d gamma m:
   mut_valid gamma m -> mut_valid (d :: gamma) m.
Proof.
  unfold mut_valid.
  intros; destruct_all; split_all; auto.
  - (*adt_inhab will change*) admit.
  - revert H1. unfold adt_positive.
    rewrite !Forall_concat, !Forall_map.
    apply Forall_impl.
    intros a.
    apply Forall_impl.
    intros fs.
    apply adt_positive_expand.
Admitted.

Lemma mut_in_ctx_expand m d gamma:
  mut_in_ctx m gamma ->
  mut_in_ctx m (d :: gamma).
Proof.
  unfold mut_in_ctx. simpl. destruct d; simpl; auto.
  intros Hin; rewrite Hin, orb_true_r; auto.
Qed.

(*This is the core: a term/formula cannot become ill-typed by
  adding more to the context*)

Lemma pattern_has_type_expand d gamma p ty:
  pattern_has_type gamma p ty ->
  pattern_has_type (d :: gamma) p ty.
Proof.
  intros Hty. induction Hty; constructor; auto;
  try apply valid_type_expand; auto.
  - clear -H. unfold sig_f in *. simpl. 
    rewrite in_app_iff; auto.
  - revert H0. apply Forall_impl. apply valid_type_expand.
Qed.

Lemma well_typed_expand d gamma t f:
  (forall ty
    (Hty: term_has_type gamma t ty),
    term_has_type (d :: gamma) t ty) /\
  ( forall (Hty: valid_formula gamma f),
    valid_formula (d :: gamma) f).
Proof.
  revert t f.
  apply term_formula_ind; intros; inversion Hty; subst;
  try solve[constructor; auto].
  - (*Tvar*)
    constructor. apply valid_type_expand. auto.
  - (*Tfun*)
    constructor; auto.
    + clear -H3. unfold sig_f in *. simpl. rewrite in_app_iff; auto.
    + revert H4. apply Forall_impl. apply valid_type_expand.
    + revert H5. apply valid_type_expand.
    + clear -H10 H. generalize dependent  (map (ty_subst (s_params f1) l) (s_args f1)).
      induction l1; simpl; intros; auto.
      destruct l0; auto.
      inversion H; subst.
      inversion H10; subst. constructor; auto.
  - (*Tmatch*)
    constructor; auto.
    + destruct H4 as [a [m [args [m_in [a_in Hv]]]]]; subst.
      exists a. exists m. exists args. split_all; auto.
      apply mut_in_ctx_expand; auto.
    + intros. apply pattern_has_type_expand; auto.
    + clear -H0 H9. induction ps; simpl; intros; auto;
      destruct H; subst;
      inversion H0; subst; simpl in H9; auto.
  - (*Teps*)
    constructor; auto. apply valid_type_expand; auto.
  - (*Fpred*)
    constructor; auto.
    + clear -H3. unfold sig_p in *. simpl. rewrite in_app_iff; auto.
    + revert H4. apply Forall_impl. apply valid_type_expand.
    + clear -H8 H. generalize dependent  (map (ty_subst (s_params p) tys) (s_args p)).
      induction tms; simpl; intros; auto.
      destruct l; auto.
      inversion H; subst.
      inversion H8; subst. constructor; auto.
  - (*Fquant*) constructor; auto. apply valid_type_expand; auto.
  - (*Fmatch*)
    constructor; auto.
    + destruct H4 as [a [m [args [m_in [a_in Hv]]]]]; subst.
      exists a. exists m. exists args. split_all; auto.
      apply mut_in_ctx_expand; auto.
    + intros. apply pattern_has_type_expand; auto.
    + clear -H0 H8. induction ps; simpl; intros; auto;
      destruct H; subst;
      inversion H0; subst; simpl in H8; auto.
Qed.

Definition term_has_type_expand d gamma t :=
  proj_tm (well_typed_expand d gamma) t.
Definition valid_formula_expand d gamma f :=
  proj_fmla (well_typed_expand d gamma) f.

Lemma funpred_def_valid_expand d gamma f:
  funpred_def_valid_type gamma f ->
  funpred_def_valid_type (d :: gamma) f.
Proof.
  unfold funpred_def_valid_type.
  destruct f; intros; destruct_all; split_all; auto.
  - apply term_has_type_expand; auto.
  - apply valid_formula_expand; auto.
Qed.

Lemma funpred_def_term_exists_expand d gamma fs:
funpred_def_term_exists gamma fs -> funpred_def_term_exists (d :: gamma) fs.
Proof.
  unfold funpred_def_term_exists.
  intros [m [params [vs [is Hdef]]]].
  exists m. exists params. exists vs. exists is.
  unfold funpred_def_term in *.
  destruct_all; split_all; auto.
  apply mut_in_ctx_expand; auto.
Qed.

Lemma funpred_valid_expand d gamma fs:
  funpred_valid gamma fs ->
  funpred_valid (d :: gamma) fs.
Proof.
  unfold funpred_valid; intros; split_all; intros.
  - revert H. apply Forall_impl. apply funpred_def_valid_expand.
  - revert H0. apply funpred_def_term_exists_expand.
Qed. 

Lemma indprop_valid_type_expand d gamma i:
  indprop_valid_type gamma i ->
  indprop_valid_type (d :: gamma) i.
Proof.
  unfold indprop_valid_type. destruct i.
  apply Forall_impl. intros; destruct_all; split_all; auto.
  apply valid_formula_expand; auto.
Qed.

Lemma indprop_valid_expand d gamma l:
  indprop_valid gamma l ->
  indprop_valid (d :: gamma) l.
Proof.
  unfold indprop_valid. intros; destruct_all; split_all; auto.
  revert H. apply Forall_impl.
  apply indprop_valid_type_expand.
Qed.

Lemma valid_def_expand d1 gamma d2:
  valid_def gamma d2 ->
  valid_def (d1 :: gamma) d2.
Proof.
  unfold valid_def. destruct d2; auto.
  - apply mut_valid_expand.
  - apply funpred_valid_expand.
  - apply indprop_valid_expand.
Qed.

End Expand.

(*Now we prove some very general lemmas about
  well-formed and valid contexts, mainly about
  diffrerent ways to use the conditions
  (which correspond to the old definitions)*)
Section ContextGenLemmas.

(*All concrete defs are in the sig*)
Lemma concrete_in_sig gamma:
  Forall (fun t => In t (sig_t gamma)) (typesyms_of_context gamma) /\
  Forall (fun f => In f (sig_f gamma)) (funsyms_of_context gamma) /\
  Forall (fun p => In p (sig_p gamma)) (predsyms_of_context gamma).
Proof.
  split_all.
  - rewrite Forall_forall.
    intros x.
    unfold typesyms_of_context, sig_t,
    datatypes_of_context, mutrec_datatypes_of_context, 
    typesyms_of_def, mut_of_context.
    rewrite !concat_map, !map_map.
    rewrite !in_concat; intros [tsl [Hintsl Hinx]].
    rewrite in_map_iff in Hintsl. exists tsl.
    destruct Hintsl as [m [Htsl Hinm]]; subst.
    split; auto.
    rewrite in_omap_iff in Hinm.
    rewrite !map_map. rewrite in_map_iff.
    destruct Hinm as [d [Hind Hd]].
    exists d.
    destruct d; inversion Hd; subst. auto.
  - rewrite Forall_forall.
    intros x.
    unfold funsyms_of_context, sig_f, funsyms_of_def.
    (*TODO: not great to have omap and list versions*)
    rewrite !in_concat. intros [fsl [Hinfsl Hinx]]; exists fsl;
    split; auto.
    rewrite in_omap_iff in Hinfsl. rewrite in_map_iff.
    destruct Hinfsl as [d [Hind Hd]]; exists d;
    destruct d; inversion Hd; subst; auto.
  - rewrite Forall_forall.
    intros x.
    unfold predsyms_of_context, sig_p, predsyms_of_def.
    rewrite !in_concat. intros [fsl [Hinfsl Hinx]]; exists fsl;
    split; auto.
    rewrite in_omap_iff in Hinfsl. rewrite in_map_iff.
    destruct Hinfsl as [d [Hind Hd]]; exists d;
    destruct d; inversion Hd; subst; auto.
Qed.

(*This lets us reason about the whole context's uniqueness
  instead of having to reason inductively*)
Lemma wf_context_alt gamma:
  wf_context gamma ->
  Forall (wf_funsym gamma) (funsyms_of_context gamma) /\
  Forall (wf_predsym gamma) (predsyms_of_context gamma) /\
  NoDup (typesyms_of_context gamma) /\
  NoDup (funsyms_of_context gamma) /\
  NoDup (predsyms_of_context gamma).
Proof.
  intros. induction H.
  - simpl. unfold funsyms_of_context, predsyms_of_context, typesyms_of_context; 
    simpl. split_all; constructor.
  - split_all.
    + clear -H0 H8. (*i think*) 
      unfold funsyms_of_context in *. simpl. destruct d; simpl;
      try rewrite Forall_app; try split; auto;
      revert H8; apply Forall_impl; intros;
      apply wf_funsym_expand; auto.
    + clear -H1 H9.
      unfold predsyms_of_context in *; simpl; destruct d; simpl;
      try rewrite Forall_app; try split; auto;
      revert H9; apply Forall_impl; intros;
      apply wf_predsym_expand; auto.
    + clear -H10 H4 H7.
      unfold typesyms_of_context, datatypes_of_context,
      mutrec_datatypes_of_context, typesyms_of_def in *. simpl.
      destruct d; simpl; auto.
      rewrite map_app, !map_map. 
      rewrite NoDup_app_iff. split_all; auto;
      (*Just need to show that these are disjoint - use previous lemma*)
      intros x Hinx1 Hinx2;
      rewrite Forall_forall in H4;
      apply (H4 x); auto;
      pose proof (concrete_in_sig gamma) as [Hall _];
      rewrite Forall_forall in Hall; apply Hall; auto.
    + clear -H11 H5 H2.
      unfold funsyms_of_context, funsyms_of_def in *. simpl.
      rewrite Forall_forall in H2.
      pose proof (concrete_in_sig gamma) as [ _ [ Hall _]].
      rewrite Forall_forall in Hall.
      destruct d; simpl; auto; rewrite NoDup_app_iff; split_all; auto;
      intros x Hinx1 Hinx2;
      apply (H2 x); auto.
    + clear -H12 H6 H3.
      unfold predsyms_of_context, predsyms_of_def in *. simpl.
      rewrite Forall_forall in H3.
      pose proof (concrete_in_sig gamma) as [ _ [ _ Hall]].
      rewrite Forall_forall in Hall.
      destruct d; simpl; auto; rewrite NoDup_app_iff; split_all; auto;
      intros x Hinx1 Hinx2;
      apply (H3 x); auto.
Qed.

(*The expand lemmas allow us to prove that all defs
  are valid with respect to the current context (not
  a previous one)*)
Lemma valid_context_defs gamma:
  valid_context gamma ->
  Forall (valid_def gamma) gamma.
Proof.
  intros Hval. induction Hval; auto.
  constructor; auto.
  revert IHHval. apply Forall_impl.
  apply valid_def_expand.
Qed.

(*Now we prove that gamma has NoDups. This follows from the
  uniqueness of each symbol type and the fact that no definition
  is empty*)
Lemma valid_context_Nodup gamma:
  valid_context gamma ->
  NoDup gamma.
Proof.
  intros Hval. induction Hval; constructor; auto.
  intros Hin.
  pose proof (concrete_in_sig gamma).
  destruct_all.
  rewrite !Forall_forall in *.
  destruct d; auto; simpl in *.
  - unfold typesyms_of_mut in H3.
    destruct (typs m) eqn : Htyps; [inversion H7 |].
    apply (H3 (adt_name a)); simpl; auto.
    apply H9.
    unfold typesyms_of_context,
    datatypes_of_context, mutrec_datatypes_of_context.
    rewrite concat_map, !map_map.
    rewrite in_concat. exists (map adt_name (typs m)).
    split; auto; [| rewrite in_map_iff; exists a; split; auto;
    rewrite Htyps; simpl; auto].
    rewrite in_map_iff. exists m. rewrite map_map. split; auto.
    apply mut_in_ctx_eq.
    apply mut_in_ctx_eq2. auto.
  - (*function - has either function or predicate symbol*)
    destruct l; [inversion H7 |].
    destruct f.
    + (*function case*)
      apply (H1 f); simpl; auto.
      apply H10. unfold funsyms_of_context.
      rewrite in_concat. exists (funsyms_of_rec (fun_def f l0 t :: l)).
      split; simpl; auto.
      rewrite in_omap_iff. exists (recursive_def (fun_def f l0 t :: l)).
      auto.
    + (*pred*)
      apply (H2 p); simpl; auto.
      apply H11. unfold predsyms_of_context.
      rewrite in_concat. exists (predsyms_of_rec (pred_def p l0 f :: l)).
      split; simpl; auto.
      rewrite in_omap_iff. exists (recursive_def (pred_def p l0 f :: l));
      auto.
  - (*inductive def has a predsym*)
    destruct l; [inversion H7 |].
    destruct i. apply (H2 p); simpl; auto.
    apply H11. unfold predsyms_of_context.
    rewrite in_concat. exists (predsyms_of_indprop (ind_def p l0 :: l)).
    split; simpl; auto.
    rewrite in_omap_iff. exists (inductive_def (ind_def p l0 :: l));
    auto.
  - apply (H3 t); auto.
    (*For abstract, use definition of sig_t*)
    unfold sig_t. rewrite in_concat. exists [t].
    split; simpl; auto.
    rewrite in_map_iff. exists (abs_type t); auto.
  - apply (H1 f); auto. unfold sig_f. rewrite in_concat.
    exists [f]. split; simpl; auto.
    rewrite in_map_iff. exists (abs_fun f); auto.
  - apply (H2 p); auto. unfold sig_p. rewrite in_concat.
    exists [p]. split; simpl; auto.
    rewrite in_map_iff. exists (abs_pred p); auto.
Qed.

End ContextGenLemmas.

(*Now, we prove that a valid context is well-ordered:
  the bodies of definitions only contain function and predicate
  symbols from earlier definitions*)
Section CtxOrder.

(*A funsym occurs in the body of a recursive function or constructor*)
Definition funsym_in_def (f: funsym) (d: def) : bool :=
  match d with
  | recursive_def fs => 
    existsb (fun x =>
      match x with
      | fun_def _ _ t => funsym_in_tm f t
      | pred_def _ _ fmla => funsym_in_fmla f fmla
      end) fs
  | inductive_def is =>
    existsb (funsym_in_fmla f) (concat (map snd (map indpred_def_to_indpred is)))
  | _ => false
  end.

Definition predsym_in_def (p: predsym) (d: def) : bool :=
  match d with
  | recursive_def fs => 
    existsb (fun x =>
      match x with
      | fun_def _ _ t => predsym_in_tm p t
      | pred_def _ _ fmla => predsym_in_fmla p fmla
      end) fs
  | inductive_def is =>
    existsb (predsym_in_fmla p) (concat (map snd (map indpred_def_to_indpred is)))
  | _ => false
  end.

(*We need that the contexts are ordered; a definition cannot
  refer to anything that comes later (mutual definitions do not count)*)
Inductive ctx_ordered : list def -> Prop :=
| ordered_nil : ctx_ordered nil
| ordered_rec: forall fs tl,
  ctx_ordered tl ->
  (forall f d,
    funsym_in_mutfun f fs ->
    In d tl ->
    ~ funsym_in_def f d
    ) ->
  (forall p d,
    predsym_in_mutfun p fs ->
    In d tl ->
    ~ predsym_in_def p d) ->
  ctx_ordered (recursive_def fs :: tl)
| ordered_indprop: forall (is: list indpred_def) tl,
  ctx_ordered tl ->
  (forall p d,
    pred_in_indpred p (get_indpred is) ->
    In d tl ->
    ~ predsym_in_def p d
  ) ->
  ctx_ordered ((inductive_def is) :: tl)
(*Other cases not interesting*)
| ordered_adt: forall m tl,
  ctx_ordered tl ->
  ctx_ordered (datatype_def m :: tl)
| ordered_abs_type: forall t tl,
  ctx_ordered tl ->
  ctx_ordered (abs_type t :: tl)
| ordered_abs_fun: forall f tl,
  ctx_ordered tl ->
  ctx_ordered (abs_fun f :: tl)
| ordered_abs_pred: forall p tl,
  ctx_ordered tl ->
  ctx_ordered (abs_pred p :: tl).

(*To prove this, we use the fact that all intermediate
  contexts are well-typed, so every symbol in them must be
  in the signature. We prove this now*)

Lemma well_typed_funsym_in_sig gamma fs t f:
  (forall ty
    (Hty: term_has_type gamma t ty) 
    (Hinfs: funsym_in_tm fs t),
    In fs (sig_f gamma)) /\
  (forall (Hty: valid_formula gamma f)
    (Hinfs: funsym_in_fmla fs f),
    In fs (sig_f gamma)).
Proof.
  revert t f; apply term_formula_ind; intros;
  inversion Hty; simpl in Hinfs;
  try solve[inversion Hinfs]; subst; auto.
  - bool_hyps. destruct Hinfs; try simpl_sumbool.
    assert (length l1 = length (map (ty_subst (s_params f1) l) (s_args f1))). {
      rewrite map_length; auto.
    }
    clear H4 H5 H7 H9 Hty H3. 
    generalize dependent (map (ty_subst (s_params f1) l) (s_args f1));
    induction l1; simpl; intros; destruct l0; inversion H1;
    simpl in H0; try discriminate.
    inversion H10; subst.
    bool_hyps. inversion H; subst.
    destruct H0; auto.
    + eapply H7. apply H5. auto.
    + apply (IHl1 H8 H0 l0); auto.
  - bool_hyps. destruct Hinfs; [apply (H (snd v)) | apply (H0 ty)]; auto.
  - repeat(bool_hyps; destruct_all); auto; [apply (H0 ty) | apply (H1 ty)]; auto.
  - bool_hyps. destruct Hinfs; [apply (H v)|]; auto.
    clear -H0 H9 H1.
    induction ps; simpl in H1;[inversion H1 |].
    bool_hyps. simpl in H9.
    inversion H0; subst.
    destruct H1; auto.
    apply (H3 ty); auto.
  - assert (length tms = length (map (ty_subst (s_params p) tys) 
      (s_args p))) by (rewrite map_length; auto).
    clear -H Hinfs H8 H0.
    generalize dependent (map (ty_subst (s_params p) tys) (s_args p));
    induction tms; simpl; intros; destruct l; inversion H0;
    simpl in Hinfs; try discriminate.
    inversion H8; inversion H; subst.
    bool_hyps.
    destruct Hinfs.
    + eapply H9. apply H4. auto.
    + apply (IHtms H10 H1 l); auto.
  - bool_hyps; destruct Hinfs; [apply (H v) | apply (H0 v)]; auto.
  - bool_hyps; destruct Hinfs; auto.
  - bool_hyps; destruct Hinfs; auto.
    apply (H (snd v)); auto.
  - repeat(bool_hyps; destruct_all); auto.
  - bool_hyps. destruct Hinfs; [apply (H v)|]; auto.
    clear -H0 H8 H1.
    induction ps; simpl in H1;[inversion H1 |].
    bool_hyps.
    simpl in H8; inversion H0; subst.
    destruct H1; auto.
Qed.

(*And the predsym version, which is very similar.
  TODO: reduce duplication somehow*)
Lemma well_typed_predsym_in_sig gamma ps t f:
  (forall ty
    (Hty: term_has_type gamma t ty) 
    (Hinfs: predsym_in_tm ps t),
    In ps (sig_p gamma)) /\
  (forall (Hty: valid_formula gamma f)
    (Hinfs: predsym_in_fmla ps f),
    In ps (sig_p gamma)).
Proof.
  revert t f; apply term_formula_ind; intros;
  inversion Hty; simpl in Hinfs;
  try solve[inversion Hinfs]; subst; auto.
  - assert (length l1 = length (map (ty_subst (s_params f1) l) (s_args f1))). {
      rewrite map_length; auto.
    }
    clear -H0 H Hinfs H10.
    generalize dependent (map (ty_subst (s_params f1) l) (s_args f1));
    induction l1; simpl; intros; destruct l0; inversion H0;
    simpl in Hinfs; try discriminate.
    inversion H10; inversion H; subst.
    bool_hyps. 
    destruct Hinfs; auto.
    + eapply H8. apply H4. auto.
    + apply (IHl1 H9 H1 l0); auto.
  - bool_hyps. destruct Hinfs; [apply (H (snd v)) | apply (H0 ty)]; auto.
  - repeat(bool_hyps; destruct_all); auto; [apply (H0 ty) | apply (H1 ty)]; auto.
  - bool_hyps. destruct Hinfs; [apply (H v)|]; auto.
    clear -H0 H9 H1.
    induction ps0; simpl in H1;[inversion H1 |].
    bool_hyps. simpl in H9; inversion H0; subst.
    destruct H1; auto.
    apply (H3 ty); auto.
  - bool_hyps. destruct Hinfs as [? | Hinfs]; try simpl_sumbool.
    assert (length tms = length (map (ty_subst (s_params p) tys) 
      (s_args p))) by (rewrite map_length; auto).
    clear -H Hinfs H8 H0.
    generalize dependent (map (ty_subst (s_params p) tys) (s_args p));
    induction tms; simpl; intros; destruct l; inversion H0;
    simpl in Hinfs; try discriminate.
    inversion H8; inversion H; subst.
    bool_hyps.
    destruct Hinfs.
    + eapply H9. apply H4. auto.
    + apply (IHtms H10 H1 l); auto.
  - bool_hyps; destruct Hinfs; [apply (H v) | apply (H0 v)]; auto.
  - bool_hyps; destruct Hinfs; auto.
  - bool_hyps; destruct Hinfs; auto.
    apply (H (snd v)); auto.
  - repeat(bool_hyps; destruct_all); auto.
  - bool_hyps. destruct Hinfs; [apply (H v)|]; auto.
    clear -H0 H8 H1.
    induction ps0; simpl in H1;[inversion H1 |].
    bool_hyps. simpl in H8; inversion H0; subst.
    destruct H1; auto.
Qed.

Definition term_has_type_funsym_in_sig gamma fs t :=
  proj_tm (well_typed_funsym_in_sig gamma fs) t.
Definition term_has_type_predsym_in_sig gamma ps t :=
  proj_tm (well_typed_predsym_in_sig gamma ps) t.
Definition valid_formula_funsym_in_sig gamma fs f :=
  proj_fmla (well_typed_funsym_in_sig gamma fs) f.
Definition valid_formula_predsym_in_sig gamma ps f :=
  proj_fmla (well_typed_predsym_in_sig gamma ps) f.

(*Any funsym or predsym in a def in a valid_context is
  in the signature*)
Definition funsym_in_def_in_sig gamma (f: funsym) d:
  valid_context gamma ->
  In d gamma ->
  funsym_in_def f d ->
  In f (sig_f gamma).
Proof.
  intros Hval Hind Hinf.
  pose proof (valid_context_defs gamma Hval) as Hdefs.
  rewrite Forall_forall in Hdefs.
  specialize (Hdefs _ Hind).
  destruct d; simpl in Hinf; try solve[inversion Hinf].
  - unfold is_true in Hinf. rewrite existsb_exists in Hinf.
    destruct Hinf as [fd [Hinfd Hfd]].
    simpl in Hdefs.
    unfold funpred_valid in Hdefs.
    destruct Hdefs as [Hty _].
    rewrite Forall_forall in Hty.
    specialize (Hty _ Hinfd).
    unfold funpred_def_valid_type in Hty.
    destruct fd; destruct_all.
    + eapply term_has_type_funsym_in_sig. apply H. auto.
    + eapply valid_formula_funsym_in_sig. apply H. auto.
  - unfold is_true in Hinf. rewrite existsb_exists in Hinf.
    destruct Hinf as [fd [Hinfd Hfd]].
    simpl in Hdefs.
    unfold funpred_valid in Hdefs.
    destruct Hdefs as [Hty _].
    rewrite Forall_forall in Hty.
    rewrite in_concat in Hinfd.
    destruct Hinfd as [fs [Hinfs Hinfd]].
    rewrite map_map in Hinfs.
    rewrite in_map_iff in Hinfs.
    destruct Hinfs as [d [Hfs Hind']]; subst.
    specialize (Hty _ Hind').
    unfold indprop_valid_type in Hty.
    destruct d; simpl in *.
    rewrite Forall_forall in Hty.
    specialize (Hty _ Hinfd).
    destruct_all.
    eapply valid_formula_funsym_in_sig. apply H. apply Hfd.
Qed.

(*Predsym version: TODO: reduce duplication - exactly
  the same except that we use the [term_has_type_predsym_in_sig]
  instead of funsym lemma*)
Definition predsym_in_def_in_sig gamma (p: predsym) d:
  valid_context gamma ->
  In d gamma ->
  predsym_in_def p d ->
  In p (sig_p gamma).
Proof.
  intros Hval Hind Hinf.
  pose proof (valid_context_defs gamma Hval) as Hdefs.
  rewrite Forall_forall in Hdefs.
  specialize (Hdefs _ Hind).
  destruct d; simpl in Hinf; try solve[inversion Hinf].
  - unfold is_true in Hinf. rewrite existsb_exists in Hinf.
    destruct Hinf as [fd [Hinfd Hfd]].
    simpl in Hdefs.
    unfold funpred_valid in Hdefs.
    destruct Hdefs as [Hty _].
    rewrite Forall_forall in Hty.
    specialize (Hty _ Hinfd).
    unfold funpred_def_valid_type in Hty.
    destruct fd; destruct_all.
    + eapply term_has_type_predsym_in_sig. apply H. auto.
    + eapply valid_formula_predsym_in_sig. apply H. auto.
  - unfold is_true in Hinf. rewrite existsb_exists in Hinf.
    destruct Hinf as [fd [Hinfd Hfd]].
    simpl in Hdefs.
    unfold funpred_valid in Hdefs.
    destruct Hdefs as [Hty _].
    rewrite Forall_forall in Hty.
    rewrite in_concat in Hinfd.
    destruct Hinfd as [fs [Hinfs Hinfd]].
    rewrite map_map in Hinfs.
    rewrite in_map_iff in Hinfs.
    destruct Hinfs as [d [Hfs Hind']]; subst.
    specialize (Hty _ Hind').
    unfold indprop_valid_type in Hty.
    destruct d; simpl in *.
    rewrite Forall_forall in Hty.
    specialize (Hty _ Hinfd).
    destruct_all.
    eapply valid_formula_predsym_in_sig. apply H. apply Hfd.
Qed.

(*And therefore, a valid context is ordered*)
Lemma valid_context_ordered gamma:
  valid_context gamma ->
  ctx_ordered gamma.
Proof.
  intros Hval. induction Hval; [| destruct d]; constructor; auto.
  - intros f d Hfinl Hind Hinfd.
    rewrite Forall_forall in H1.
    apply (H1 f). simpl. apply in_bool_In in Hfinl; auto. 
    eapply funsym_in_def_in_sig; auto. apply Hind. auto.
  - intros p d Hpinl Hind Hinpd.
    rewrite Forall_forall in H2.
    apply (H2 p); simpl. apply in_bool_In in Hpinl; auto.
    eapply predsym_in_def_in_sig; auto. apply Hind. auto.
  - intros p d Hpinl Hind Hinpd.
    rewrite Forall_forall in H2.
    apply (H2 p). simpl. apply pred_in_indpred_iff; auto.
    eapply predsym_in_def_in_sig; auto. apply Hind. auto.
Qed. 
 
End CtxOrder.

(*Now we prove a variety of more specific lemmas we need
  later that deal with specific parts of the context*)

(*First, prove lemmas about wf_contexts (not valid)*)
Section WFContextLemmas.

Context {gamma: context} (gamma_wf: wf_context gamma).

(*If m1 and m2 have an ADT name in common, they are equal*)
Lemma mut_adts_inj {m1 m2: mut_adt} {a1 a2: alg_datatype}:
  mut_in_ctx m1 gamma ->
  mut_in_ctx m2 gamma ->
  adt_in_mut a1 m1 ->
  adt_in_mut a2 m2 ->
  adt_name a1 = adt_name a2 ->
  m1 = m2.
Proof.
  intros m_in1 m_in2 a_in1 a_in2 Heq.
  apply wf_context_alt in gamma_wf.
  destruct gamma_wf as [_ [_ [Hnodup _]]].
  (*Search wf_context.
  destruct gamma_wf as [_ [_ [_ [_ [Hnodup _]]]]].*)
  unfold typesyms_of_context, datatypes_of_context,
  mutrec_datatypes_of_context in Hnodup.
  rewrite concat_map in Hnodup.
  rewrite map_map in Hnodup.
  rewrite NoDup_concat_iff in Hnodup.
  rewrite map_length in Hnodup.
  destruct Hnodup as [_ Hnodup].
  rewrite mut_in_ctx_eq in m_in1, m_in2.
  assert (m: mut_adt) by (apply m1).
  destruct (In_nth _ _ m m_in1) as [i [Hi Hith]].
  destruct (In_nth _ _ m m_in2) as [j [Hj Hjth]].
  destruct (Nat.eq_dec i j). {
    (*If i=j, easy*)
    subst; auto.
  }
  specialize (Hnodup i j nil (adt_name a1) Hi Hj n).
  exfalso. apply Hnodup; clear Hnodup.
  rewrite !map_nth_inbound with(d2:=m); auto.
  rewrite <- mut_in_ctx_eq in m_in1, m_in2.
  rewrite Hith, Hjth, !map_map; simpl; split;
  rewrite in_map_iff; [exists a1 | exists a2]; split; auto;
  apply (in_bool_In adt_dec); auto.
Qed.

(*The syms in the [funpred_defs_to_sns] are unique*)
Lemma funpred_defs_to_sns_NoDup (l: list funpred_def) il:
  In l (mutfuns_of_context gamma) ->
  length l = length il ->
  NoDup (map fn_sym (fst (funpred_defs_to_sns l il))) /\
  NoDup (map pn_sym (snd (funpred_defs_to_sns l il))).
Proof.
  apply wf_context_alt in gamma_wf.
  intros Hinl Hlen.
  destruct gamma_wf as [_ [_ [_ [Hwf1 Hwf2]]]].
  unfold funsyms_of_context in Hwf1.
  unfold predsyms_of_context in Hwf2.
  unfold funpred_defs_to_sns; simpl; rewrite !map_map; simpl.
  pose proof (split_funpred_defs_length l) as Hlenfstsnd.
  rewrite !map_fst_fst_fst_combine; [| rewrite skipn_length | rewrite firstn_length]; try lia.
  rewrite !NoDup_concat_iff in Hwf1.
  rewrite !NoDup_concat_iff in Hwf2.
  destruct Hwf1 as [Hwf1 _ ].
  destruct Hwf2 as [Hwf2 _].
  assert (Hin: In (recursive_def l) gamma). {
    apply in_mutfuns. auto.
  }
  split; [apply Hwf1 | apply Hwf2]; rewrite in_omap_iff;
  exists (recursive_def l); split; auto; f_equal; clear;
  induction l; simpl; auto; destruct a; simpl; auto;
  rewrite IHl; reflexivity.
Qed.

Lemma fundef_inj (l: list funpred_def) (f: funsym)
  (a1 a2: list vsymbol) (b1 b2: term):
  In l (mutfuns_of_context gamma) ->
  In (fun_def f a1 b1) l ->
  In (fun_def f a2 b2) l ->
  a1 = a2 /\ b1 = b2.
Proof.
  apply wf_context_alt in gamma_wf.
  intros l_in Hin1 Hin2.
  destruct gamma_wf as [_ [_ [_ [Hwf1 _]]]].
  unfold funsyms_of_context in Hwf1.
  rewrite NoDup_concat_iff in Hwf1.
  destruct Hwf1 as [Hwf _].
  assert (Hin: In (recursive_def l) gamma). {
    apply in_mutfuns; auto.
  }
  specialize (Hwf (funsyms_of_rec l)).
  prove_hyp Hwf.
  {
    rewrite in_omap_iff. exists (recursive_def l); auto.
  }
  (*TODO: separate lemma or induction?*)
  simpl in Hwf.
  clear -Hwf Hin1 Hin2.
  induction l; [inversion Hin1 |].
  simpl in *. destruct a.
  2: {
    destruct Hin1; destruct Hin2; try solve[inversion H];
    try solve[inversion H0]; auto.
  }
  inversion Hwf; subst.
  destruct Hin1; destruct Hin2; auto.
  - inversion H; inversion H0; subst; auto.
  - exfalso. apply H1.
    inversion H; subst.
    apply (in_fun_def l _ _ _ H0).
  - inversion H0; subst.
    exfalso. apply H1.
    apply (in_fun_def l _ _ _ H).
Qed.

Lemma preddef_inj (l: list funpred_def) (p: predsym)
  (a1 a2: list vsymbol) (b1 b2: formula):
  In l (mutfuns_of_context gamma) ->
  In (pred_def p a1 b1) l ->
  In (pred_def p a2 b2) l ->
  a1 = a2 /\ b1 = b2.
Proof.
  apply wf_context_alt in gamma_wf.
  intros l_in Hin1 Hin2.
  destruct gamma_wf as [_ [_ [_ [_ Hwf1]]]].
  unfold predsyms_of_context in Hwf1.
  rewrite NoDup_concat_iff in Hwf1.
  destruct Hwf1 as [Hwf _].
  assert (Hin: In (recursive_def l) gamma). {
    apply in_mutfuns; auto.
  }
  specialize (Hwf (predsyms_of_rec l)).
  prove_hyp Hwf.
  { rewrite in_omap_iff. exists (recursive_def l); auto. }
  (*TODO: separate lemma or induction?*)
  clear -Hwf Hin1 Hin2.
  induction l; [inversion Hin1 |].
  simpl in Hin1, Hin2.
  simpl in *. destruct a.
  {
    destruct Hin1; destruct Hin2; try solve[inversion H];
    try solve[inversion H0]; auto.
  }
  inversion Hwf; subst.
  destruct Hin1; destruct Hin2; auto.
  - inversion H; inversion H0; subst; auto.
  - exfalso. apply H1.
    inversion H; subst.
    apply (in_pred_def l _ _ _ H0).
  - inversion H0; subst.
    exfalso. apply H1.
    apply (in_pred_def l _ _ _ H).
Qed.

End WFContextLemmas.

Section ValidContextLemmas.

Context {gamma: context} (gamma_valid: valid_context gamma).

(*These lemmas all have the same form: keep applying Forall_forall, in_map_iff,
  and similar, until we get what we want. Here we automate them*)
(*Ltac valid_context_tac :=
  let Hwf := fresh "Hwf" in
  let Hadts := fresh "Hadts" in
  destruct gamma_valid as [Hwf Hadts];
  rewrite Forall_forall in Hadts;
  unfold adt_in_mut, constr_in_adt in *;
  repeat match goal with
  | Hin: is_true (mut_in_ctx ?m ?l) |- _ => 
    rewrite mut_in_ctx_eq2 in Hin
  | Hin: is_true (in_bool adt_dec ?x ?l) |- _ =>
    let Hinx := fresh "Hin" in
    assert (Hinx: In x l) by (apply (in_bool_In _  _ _ Hin));
    clear Hin
  | Hin: In ?x (?p gamma) |- _ => unfold p in Hin
  | Hin: In ?x (concat ?l) |- _ => rewrite in_concat in Hin
  | Hex: exists x, ?p |- _ => destruct Hex; subst
  | Hconj: ?P /\ ?Q |- _ => destruct Hconj; subst
  | Hmap: In ?x (map ?f ?l) |- _ => rewrite in_map_iff in Hmap
  | Hgam: In ?x gamma |- _ => apply Hadts in Hgam
  | Hdef: def |- _ => destruct Hdef; simpl in *
  | Halg: match ?x with | alg_def ts fs => ?p end = ?q |- _ => 
    destruct x; inversion Halg; subst; clear Halg
  | Halg: match ?x with | alg_def ts fs => ?p end |- _ => destruct x
  | Hf: False |- _ => destruct Hf
  | Hall: Forall ?P ?l |- _ => rewrite Forall_forall in Hall
  | Hin: In ?x ?l, Hall: forall x : ?t, In x ?l -> ?P |- _ =>
    specialize (Hall _ Hin)
  end; auto.*)

Ltac valid_ctx_info :=
  let Hwf := fresh "Hwf" in
  pose proof (valid_context_wf _ gamma_valid) as Hwf;
  apply wf_context_alt in Hwf;
  destruct Hwf as [Hvalf [Hvalp [Hn1 [Hn2 Hn3]]]];
  let Hvald := fresh "Hvald" in
  pose proof (valid_context_defs _ gamma_valid) as Hvald.

Ltac apply_forall :=
  match goal with
  | H: Forall ?P ?l, H1: In ?x ?l |- _ =>
    rewrite Forall_forall in H;
    let H2 := fresh in
    assert (H2: P x) by (apply H; apply H1);
    simpl in H2
  end.

Ltac simpl_val :=
  repeat match goal with
  | H: valid_def ?g ?d |- _ => unfold valid_def in H
  | H: mut_valid ?g ?m |- _ => unfold mut_valid in H
  | H: valid_mut_rec ?m |- _ => unfold valid_mut_rec in H
  | H: adt_valid_type ?a |- _ => unfold adt_valid_type in H
  end.

Ltac valid_context_tac :=
  repeat(repeat apply_forall;
  simpl_val;
  destruct_all).

Lemma adt_args: forall {m: mut_adt} {a: alg_datatype}
  (Hin: adt_mut_in_ctx a m gamma),
  ts_args (adt_name a) = m_params m.
Proof.
  intros. unfold adt_mut_in_ctx in Hin. destruct Hin.
  valid_ctx_info.
  rewrite mut_in_ctx_eq2 in H0.
  unfold adt_in_mut in H.
  apply in_bool_In in H.
  valid_context_tac.
  auto.
Qed.

(*TODO: move*)
Lemma constr_in_adt_eq c a:
  constr_in_adt c a <-> In c (adt_constr_list a).
Proof.
  unfold constr_in_adt.
  rewrite in_bool_ne_equiv.
  rewrite (reflect_iff _ _ (in_bool_spec funsym_eq_dec _ _)).
  reflexivity.
Qed.

Lemma adt_constr_params: forall {m: mut_adt} {a: alg_datatype}
  {c: funsym} (Hm: mut_in_ctx m gamma)
  (Ha: adt_in_mut a m)
  (Hc: constr_in_adt c a),
  s_params c = m_params m.
Proof.
  intros. unfold adt_in_mut in Ha.
  valid_ctx_info.
  rewrite mut_in_ctx_eq2 in Hm.
  apply in_bool_In in Ha.
  rewrite constr_in_adt_eq in Hc.
  valid_context_tac. auto.
Qed.

Lemma adt_constr_ret: forall {m: mut_adt} {a: alg_datatype}
  {c: funsym} (Hm: mut_in_ctx m gamma) (Ha: adt_in_mut a m) 
  (Hc: constr_in_adt c a),
  f_ret c = vty_cons (adt_name a) (map vty_var (m_params m)).
Proof.
  intros.
  unfold adt_in_mut in Ha.
  rewrite mut_in_ctx_eq2 in Hm.
  apply in_bool_In in Ha.
  apply in_bool_ne_In in Hc.
  valid_ctx_info.
  valid_context_tac.
  destruct a; simpl in *.
  valid_context_tac.
  rewrite H8, H9. 
  auto.
Qed.

Lemma adts_names_nodups: forall {m: mut_adt}
  (Hin: mut_in_ctx m gamma),
  NoDup (map adt_name (typs m)).
Proof.
  intros. 
  valid_ctx_info.
  clear -Hn1 Hin.
  unfold typesyms_of_context, datatypes_of_context,
  mutrec_datatypes_of_context in Hn1.
  rewrite concat_map, NoDup_concat_iff in Hn1.
  destruct Hn1 as [Hn _].
  apply Hn. rewrite !map_map. rewrite in_map_iff.
  exists m. split.
  - rewrite map_map. reflexivity.
  - apply mut_in_ctx_eq; auto.
Qed.

Lemma adts_nodups: forall {m: mut_adt}
  (Hin: mut_in_ctx m gamma),
  NoDup (typs m).
Proof.
  intros.
  eapply NoDup_map_inv. apply adts_names_nodups. apply Hin.
Qed.

(*TODO: move - some lemmas about NoDup and concat*)

Lemma NoDup_concat: forall {A: Type}
  (eq_dec: forall (x y: A), {x = y} + {x <> y})
{l: list (list A)} 
  {l1: list A},
  NoDup (concat l) ->
  In l1 l ->
  NoDup l1.
Proof.
  intros A eq_dec; induction l; intros; simpl; auto.
  - destruct H0. 
  - simpl in H. simpl in H0.
    rewrite NoDup_app_iff in H.
    destruct H as [Hna [Hnc [Hina Hinc]]].
    destruct H0; subst.
    + assumption.
    + apply IHl; assumption.
Qed.

Lemma NoDup_concat': forall {A: Type}
  (eq_dec: forall (x y: A), {x = y} + {x <> y})
{l: list (list A)} 
  {l1: list (list A)} {l2: list A},
  NoDup (concat l) ->
  In (concat l1) l ->
  In l2 l1 ->
  NoDup l2.
Proof.
  intros.
  assert (NoDup (concat l1)). apply (NoDup_concat eq_dec H H0).
  apply (NoDup_concat eq_dec H2 H1).
Qed.

Lemma constrs_nodups: forall {m: mut_adt} {constrs: ne_list funsym}
  {m_in: mut_in_ctx m gamma}
  (Hin: In constrs (map adt_constrs (typs m))),
  nodupb funsym_eq_dec (ne_list_to_list constrs).
Proof.
  intros.
  apply (reflect_iff _ _ (nodup_NoDup _ _)).
  rewrite in_map_iff in Hin. destruct Hin as [a [Ha Hina]]; subst.
  valid_ctx_info.
  clear -Hn2 m_in Hina.
  unfold funsyms_of_context in Hn2.
  assert (Hin: In (ne_list_to_list (adt_constrs a))
  (map adt_constr_list (typs m))). {
    rewrite in_map_iff. exists a. split; auto.
  }
  eapply NoDup_concat'. apply funsym_eq_dec. apply Hn2.
  2: apply Hin.
  rewrite in_omap_iff. exists (datatype_def m).
  split; auto. apply mut_in_ctx_eq2; auto.
Qed.

Lemma pat_has_type_valid: forall p ty,
  pattern_has_type gamma p ty ->
  valid_type gamma ty.
Proof.
  intros. induction H; try assumption; auto.
  apply valid_type_subst; auto.
Qed.

(*If a term has a type, that type is well-formed. We need the 
  [valid_pat_fmla] or else we could have an empty pattern*)
Lemma has_type_valid: forall (*s gamma*) t ty,
  (*well_typed_term s gamma t ty ->*)
  term_has_type gamma t ty ->
  valid_type gamma ty.
Proof.
  intros. induction H; try solve[constructor]; try assumption; auto.
  apply valid_type_subst; assumption.
  destruct ps. inversion H4.
  apply (H3 p); auto. left; auto. 
Qed.

(*TODO: START*)
  
(*All constrs are in [funsym_of_context gamma]*)
Lemma constrs_in_funsyms: forall {gamma c a m},
  mut_in_ctx m gamma ->
  adt_in_mut a m ->
  constr_in_adt c a ->
  In c (funsyms_of_context gamma).
Proof.
  clear.
  intros gamma c a m. unfold adt_in_mut, constr_in_adt.
  intros m_in a_in c_in; induction gamma; simpl. inversion m_in.
  simpl in m_in. unfold funsyms_of_context in *. simpl.
  rewrite mut_in_ctx_eq2 in m_in.
  destruct m_in as [Ha0 | m_in]; [| apply in_or_app; right; auto].
  subst. apply in_or_app; left. simpl.
  rewrite in_concat. exists (ne_list_to_list (adt_constrs a)).
  rewrite in_map_iff. split; [| eapply in_bool_ne_In; apply c_in].
  exists a. split; auto. destruct a. reflexivity.
  apply (in_bool_In _ _ _ a_in).
  apply IHc0. apply mut_in_ctx_eq2; auto.
Qed. 

(*All constr args types are valid*)
Lemma constr_ret_valid: forall {c a m},
  mut_in_ctx m gamma ->
  adt_in_mut a m ->
  constr_in_adt c a ->
  forall x, In x (s_args c) -> valid_type s x.
Proof.
  intros c a m m_in a_in c_in x Hinx.
  unfold valid_context in gamma_valid.
  unfold wf_context in gamma_valid.
  destruct gamma_valid as [[Hsig [_ [Hfuns _]]] _].
  clear gamma_valid.
  unfold wf_sig in Hsig.
  destruct Hsig as [Hsig _].
  rewrite Forall_forall in Hsig, Hfuns.
  assert (Hinsig: In c (sig_f s)). {
    apply Hfuns. apply (constrs_in_funsyms m_in a_in c_in).
  }
  clear Hfuns. specialize (Hsig _ Hinsig).
  rewrite Forall_forall in Hsig. apply Hsig. right; auto.
Qed. 




(*TODO: have similar lemma in IndTypes but for finite version*)
Lemma adt_names_inj' {a1 a2: alg_datatype} {m: mut_adt}:
  adt_in_mut a1 m ->
  adt_in_mut a2 m ->
  mut_in_ctx m gamma ->
  adt_name a1 = adt_name a2 ->
  a1 = a2.
Proof.
  intros. assert (NoDup (map adt_name (typs m))) by
    apply (adts_names_nodups H1). 
  apply (@NoDup_map_in _ _ _ _ a1 a2) in H3; auto.
  apply (in_bool_In _ _ _ H).
  apply (in_bool_In _ _ _ H0).
Qed.

(*
Definition constrs_ne: forall {l: list (typesym * list funsym)}
  (Hin: In l (mutrec_datatypes_of_context gamma)),
  forallb (fun b => negb (null b)) (map snd l).
Proof.
  intros. apply forallb_forall. intros.
  valid_context_tac.
  unfold adt_inhab in H1.
  valid_context_tac. simpl.
Qed.*)

(*Stuff for recursive functions*)

Lemma in_mutfuns_spec: forall l gamma',
  In l (mutfuns_of_context gamma') <-> In (recursive_def l) gamma'.
Proof.
  intros. induction gamma'; simpl; intros; [split; auto |].
  destruct a; simpl.
  - split; intros; [apply IHgamma' in H; auto| 
      destruct_all; try discriminate; apply IHgamma'; auto].
  - split; intros; destruct_all; subst; auto; [apply IHgamma' in H; auto| 
      destruct_all; try discriminate; inversion H; auto |
      right; apply IHgamma'; auto].
  - split; intros; [apply IHgamma' in H; auto| 
      destruct_all; try discriminate; apply IHgamma'; auto].
Qed.

Lemma all_funpred_def_valid_type l:
  In l (mutfuns_of_context gamma) ->
  Forall (funpred_def_valid_type s gamma) l.
Proof.
  intros. unfold valid_context in gamma_valid.
  destruct gamma_valid as [_ Hall].
  rewrite in_mutfuns_spec in H.
  rewrite Forall_forall in Hall.
  specialize (Hall _ H). simpl in Hall.
  apply Hall.
Qed. 

Lemma constr_in_adt_def a m f:
  adt_in_mut a m ->
  constr_in_adt f a ->
  In f (funsyms_of_def (datatype_def m)).
Proof.
  unfold mut_in_ctx. unfold adt_in_mut. unfold constr_in_adt.
  intros a_in c_in.
  apply in_bool_In in a_in.
  apply in_bool_ne_In in c_in.
  simpl. induction (typs m); simpl in *. destruct a_in.
  destruct a0. destruct a_in; subst.
  - rewrite in_app_iff. left. apply c_in.
  - rewrite in_app_iff. right. apply IHl. auto.
Qed. 

(*Default def*)
Definition def_d : def := recursive_def nil.

(*Lemmas about NoDups/uniqueness*)
Section UniqLemmas.

(*NOTE: really, these only require wf_context. Maybe move later.*)

(*A constructor and a recursive function cannot have
  the same name*)
Lemma constr_not_recfun (l: list funpred_def) (f: funsym) 
  (a: alg_datatype)
  (m: mut_adt) (l_in: In l (mutfuns_of_context gamma))
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (f_in1: funsym_in_mutfun f l) (f_in2: constr_in_adt f a):
  False.
Proof.
  destruct gamma_valid as [Hwf _].
  destruct Hwf as [_ [_[_ [_ [ _ [Hnodup _]]]]]].
  unfold funsyms_of_context in Hnodup.
  rewrite NoDup_concat_iff in Hnodup.
  destruct Hnodup as [_ Hnodup].
  apply in_bool_In in m_in.
  unfold funsym_in_mutfun in f_in1.
  apply in_bool_In in f_in1.
  pose proof (constr_in_adt_def _ _ _ a_in f_in2) as f_in2'.
  assert (Hin1: In (recursive_def l) gamma). {
    apply in_mutfuns_spec. apply l_in.
  }
  assert (Hin2: In (datatype_def m) gamma). {
    apply mut_in_ctx_eq2. apply In_in_bool. apply m_in. 
  }
  destruct (In_nth _ _ def_d Hin1) as [i1 [Hi1 Hrecdef]].
  destruct (In_nth _ _ def_d Hin2) as [i2 [Hi2 Hdatdef]].
  destruct (Nat.eq_dec i1 i2).
  - subst. rewrite Hdatdef in Hrecdef. inversion Hrecdef.
  - apply (Hnodup i1 i2 nil f); try rewrite map_length; auto.
    rewrite !map_nth_inbound with (d2:=def_d); auto.
    rewrite Hrecdef, Hdatdef. auto.
Qed.

(*A recursive function name cannot appear in two different
  mutually recursive function blocks*)
Lemma recfun_not_twice f l1 l2:
  In (recursive_def l1) gamma ->
  In (recursive_def l2) gamma ->
  funsym_in_mutfun f l1 ->
  funsym_in_mutfun f l2 ->
  l1 = l2.
Proof.
  intros.
  destruct gamma_valid as [Hwf _].
  unfold wf_context in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ [Hnodup _]]]]]].
  unfold funsyms_of_context in Hnodup.
  rewrite NoDup_concat_iff in Hnodup.
  destruct Hnodup as [_ Hn].
  rewrite map_length in Hn.
  destruct (In_nth _ _ def_d H) as [i1 [Hi1 Hl1]].
  destruct (In_nth _ _ def_d H0) as [i2 [Hi2 Hl2]].
  destruct (Nat.eq_dec i1 i2); subst.
  {
    rewrite Hl1 in Hl2. inversion Hl2; auto.
  }
  exfalso. apply (Hn _ _ nil f Hi1 Hi2 n).
  rewrite !map_nth_inbound with(d2:=def_d); auto.
  rewrite Hl1, Hl2.
  split; apply in_bool_In with(eq_dec:=funsym_eq_dec); auto.
Qed.

(*Same for recursive preds*)
Lemma recpred_not_twice p l1 l2:
  In (recursive_def l1) gamma ->
  In (recursive_def l2) gamma ->
  predsym_in_mutfun p l1 ->
  predsym_in_mutfun p l2 ->
  l1 = l2.
Proof.
  intros.
  destruct gamma_valid as [Hwf _].
  unfold wf_context in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ [_ Hnodup]]]]]].
  unfold predsyms_of_context in Hnodup.
  rewrite NoDup_concat_iff in Hnodup.
  destruct Hnodup as [_ Hn].
  rewrite map_length in Hn.
  destruct (In_nth _ _ def_d H) as [i1 [Hi1 Hl1]].
  destruct (In_nth _ _ def_d H0) as [i2 [Hi2 Hl2]].
  destruct (Nat.eq_dec i1 i2); subst.
  {
    rewrite Hl1 in Hl2. inversion Hl2; auto.
  }
  exfalso. apply (Hn _ _ nil p Hi1 Hi2 n).
  rewrite !map_nth_inbound with(d2:=def_d); auto.
  rewrite Hl1, Hl2.
  split; apply in_bool_In with(eq_dec:=predsym_eq_dec); auto.
Qed.

(*A recursive function cannot have the same name as an
  inductive predicate*)
Lemma recpred_not_indpred p l1 l2:
  In (recursive_def l1) gamma ->
  In (inductive_def l2) gamma ->
  predsym_in_mutfun p l1 ->
  ~ pred_in_indpred p (get_indpred l2).
Proof.
  intros. intros Hinp'.
  destruct gamma_valid as [Hwf _].
  unfold wf_context in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ [_ Hnodup]]]]]].
  unfold predsyms_of_context in Hnodup.
  rewrite NoDup_concat_iff in Hnodup.
  destruct Hnodup as [_ Hn].
  rewrite map_length in Hn.
  destruct (In_nth _ _ def_d H) as [i1 [Hi1 Hl1]].
  destruct (In_nth _ _ def_d H0) as [i2 [Hi2 Hl2]].
  destruct (Nat.eq_dec i1 i2); subst.
  {
    rewrite Hl1 in Hl2. inversion Hl2.
  }
  apply (Hn _ _ nil p Hi1 Hi2 n).
  rewrite !map_nth_inbound with(d2:=def_d); auto.
  rewrite Hl1, Hl2.
  split. apply in_bool_In with(eq_dec:=predsym_eq_dec); auto.
  simpl. rewrite in_map_iff.
  unfold pred_in_indpred in Hinp'.
  apply in_bool_In in Hinp'.
  rewrite in_map_iff in Hinp'.
  destruct Hinp' as [[p' fs] [Hp Hinp']];
  simpl in *; subst.
  unfold get_indpred in Hinp'.
  rewrite in_map_iff in Hinp'.
  destruct Hinp' as [d'[Hdx Hind]].
  exists d'. 
  destruct d'; simpl in *; inversion Hdx; subst; split; auto.
Qed.

(*A constructor cannot appear in two different adts*)
Lemma constr_in_one_adt 
  (c: funsym) (m1 m2: mut_adt) (a1 a2: alg_datatype)
  (m_in1: mut_in_ctx m1 gamma)
  (m_in2: mut_in_ctx m2 gamma)
  (a_in1: adt_in_mut a1 m1)
  (a_in2: adt_in_mut a2 m2)
  (c_in1: constr_in_adt c a1)
  (c_in2: constr_in_adt c a2):
  a1 = a2 /\ m1 = m2.
Proof.
  (*Handle easy case first*)
  destruct (adt_dec a1 a2); subst.
  {
    split; auto. apply (@mut_adts_inj _ _ (proj1 gamma_valid) _ _ a2 a2); auto.
  }
  destruct gamma_valid as [Hwf _].
  destruct Hwf as [_ [_ [_ [_ [_ [Hnodup _]]]]]].
  unfold funsyms_of_context in Hnodup.
  rewrite NoDup_concat_iff in Hnodup.
  (*If m1 and m2 are the same, look within def, otherwise between defs*)
  destruct (mut_adt_dec m1 m2); subst.
  - split; auto.
    destruct Hnodup as [Hnodup _].
    assert (In (datatype_def m2) gamma) by (apply mut_in_ctx_eq2; auto).
    specialize (Hnodup (funsyms_of_def (datatype_def m2))).
    assert (In (funsyms_of_def (datatype_def m2)) (map funsyms_of_def gamma)).
      rewrite in_map_iff. exists (datatype_def m2); auto.
    specialize (Hnodup H0).
    simpl in Hnodup.
    rewrite NoDup_concat_iff in Hnodup.
    rewrite map_length in Hnodup.
    (*Look across, not in, adts*)
    destruct Hnodup as [_ Hnodup].
    exfalso.
    assert (Hin1: In a1 (typs m2)) by (apply in_bool_In in a_in1; auto).
    assert (Hin2: In a2 (typs m2)) by (apply in_bool_In in a_in2; auto).
    destruct (In_nth _ _ a1 Hin1) as [i1 [Hi1 Ha1]].
    destruct (In_nth _ _ a2 Hin2) as [i2 [Hi2 Ha2]].
    (*Easy contradiction if i1 = i2*)
    destruct (Nat.eq_dec i1 i2); subst.
    {
      apply n. rewrite <- Ha1. rewrite <- Ha2. apply nth_indep. auto.
    }
    apply (Hnodup i1 i2 nil c Hi1 Hi2 n0).
    rewrite map_nth_inbound with(d2:=a1); auto.
    rewrite map_nth_inbound with(d2:=a2); auto.
    rewrite Ha1, Ha2.
    unfold constr_in_adt in c_in1, c_in2.
    destruct a1; destruct a2; simpl in *; split; apply in_bool_ne_In
    with(eq_dec:=funsym_eq_dec); auto.
  - (*This time in different m1 and m2*)
    destruct Hnodup as [_ Hnodup].
    rewrite map_length in Hnodup.
    assert (Hin1: In (datatype_def m1) gamma) by (apply mut_in_ctx_eq2; auto).
    assert (Hin2: In (datatype_def m2) gamma) by (apply mut_in_ctx_eq2; auto).
    destruct (In_nth _ _ def_d Hin1) as [i1 [Hi1 Hm1]].
    destruct (In_nth _ _ def_d Hin2) as [i2 [Hi2 Hm2]].
    destruct (Nat.eq_dec i1 i2); subst.
    {
      rewrite Hm1 in Hm2. inversion Hm2; subst; contradiction.
    }
    exfalso.
    apply (Hnodup i1 i2 nil c Hi1 Hi2 n1).
    rewrite !map_nth_inbound with (d2:=def_d); auto.
    rewrite Hm1, Hm2.
    split; [apply constr_in_adt_def with(a:=a1) |
    apply constr_in_adt_def with (a:=a2)]; auto.
Qed.

End UniqLemmas.

Lemma gamma_all_unif: forall m, mut_in_ctx m gamma ->
  uniform m.
Proof.
  destruct gamma_valid as [_ Hval].
  intros m Hm.
  apply mut_in_ctx_eq2 in Hm.
  rewrite Forall_forall in Hval.
  specialize (Hval _ Hm).
  simpl in Hval.
  destruct_all; auto.
Qed.

End ValidContextLemmas.

Section GetADT.

Variable gamma: context.

(*Get ADT of a type*)

Definition find_ts_in_ctx (ts: typesym) : option (mut_adt * alg_datatype) :=
  fold_right (fun m acc => 
    match (find_ts_in_mut ts m) with
    | Some a => Some (m, a)
    | None => acc
    end) None (mut_of_context gamma).

Definition is_vty_adt (ty: vty) : 
  option (mut_adt * alg_datatype * list vty) :=
  match ty with
  | vty_cons ts tys =>
    match (find_ts_in_ctx ts) with
    | Some (m, a) => Some (m, a, tys)
    | None => None
    end
  | _ => None
  end.

Lemma vty_m_adt_some (m: mut_adt) (vs: list vty) (v: vty) a:
  vty_m_adt m vs v = Some a ->
  adt_in_mut a m /\ v = vty_cons (adt_name a) vs.
Proof.
  intros. unfold vty_m_adt in H.
  destruct v; try discriminate.
  destruct (list_eq_dec vty_eq_dec l vs); subst; try discriminate.
  apply find_ts_in_mut_some in H. destruct H; subst; auto.
Qed.

Lemma vty_m_adt_none (m: mut_adt) (vs: list vty) (v: vty):
  vty_m_adt m vs v = None ->
  (forall a, adt_in_mut a m -> v <> vty_cons (adt_name a) vs).
Proof.
  intros. unfold vty_m_adt in H. destruct v; try discriminate.
  destruct (list_eq_dec vty_eq_dec l vs); subst; try (intro C; inversion C; subst; contradiction).
  rewrite find_ts_in_mut_none in H.
  intro C; inversion C; subst.
  apply (H _ H0); auto.
Qed.

(*Weaker specs - no well-formed context*)
Lemma find_ts_in_ctx_none (ts: typesym):
  reflect (forall (a: alg_datatype) (m: mut_adt),
    mut_in_ctx m gamma -> adt_in_mut a m ->
    adt_name a <> ts) (negb (ssrbool.isSome (find_ts_in_ctx ts))).
Proof.
  unfold find_ts_in_ctx, mut_in_ctx.
  induction (mut_of_context gamma); simpl.
  - apply ReflectT. intros a m H; inversion H.
  - destruct (find_ts_in_mut ts a) eqn : Hinmut; simpl.
    + apply ReflectF. intro C.
      apply find_ts_in_mut_some in Hinmut.
      destruct Hinmut. subst. apply (C a0 a); auto.
      rewrite eq_dec_refl; auto. 
    + rewrite find_ts_in_mut_none in Hinmut. 
      destruct IHl.
      * apply ReflectT. intros.
        destruct (mut_adt_dec m a); simpl in H; subst.
        apply (Hinmut _ H0); auto.
        apply (n _ m); auto.
      * apply ReflectF. intros C.
        apply n. intros a' m Hin. apply C. 
        rewrite Hin, orb_true_r. auto.
Qed.

Lemma find_ts_in_ctx_none_iff (ts: typesym):
  (forall (a: alg_datatype) (m: mut_adt),
    mut_in_ctx m gamma -> adt_in_mut a m ->
    adt_name a <> ts) <-> find_ts_in_ctx ts = None.
Proof.
  rewrite (reflect_iff _ _ (find_ts_in_ctx_none ts)).
  destruct (find_ts_in_ctx ts); simpl; split; intros; auto; discriminate.
Qed.

Lemma find_ts_in_ctx_some (ts: typesym) m a:
  find_ts_in_ctx ts = Some (m, a) ->
  mut_in_ctx m gamma /\ adt_in_mut a m /\
  ts = adt_name a.
Proof.
  unfold find_ts_in_ctx, mut_in_ctx.
  induction (mut_of_context gamma); simpl; auto; intros; try discriminate.
  destruct (find_ts_in_mut ts a0) eqn : Hfind.
  - inversion H; subst.
    apply find_ts_in_mut_some in Hfind. destruct_all.
    rewrite eq_dec_refl; auto.
  - apply IHl in H. destruct_all; subst. split; auto.
    rewrite H, orb_true_r; auto.
Qed.

Lemma is_vty_adt_none (ty: vty):
  reflect (forall a m vs,
    mut_in_ctx m gamma ->
    adt_in_mut a m ->
    ty <> vty_cons (adt_name a) vs) 
  (negb (ssrbool.isSome (is_vty_adt ty))).
Proof.
  unfold is_vty_adt.
  destruct ty; simpl; try (apply ReflectT; intros; discriminate).
  destruct (find_ts_in_ctx t) eqn : Hfind.
  - destruct p as [m a]. simpl. apply ReflectF.
    apply find_ts_in_ctx_some in Hfind.
    destruct_all.
    intro.
    apply (H1 a m l); auto.
  - simpl. apply ReflectT.
    rewrite <- find_ts_in_ctx_none_iff in Hfind.
    intros.
    intro C; inversion C; subst.
    apply (Hfind a m); auto.
Qed.

Lemma is_vty_adt_none_iff (ty: vty):
  (forall a m vs,
  mut_in_ctx m gamma ->
  adt_in_mut a m ->
  ty <> vty_cons (adt_name a) vs) <->
  is_vty_adt ty = None.
Proof.
  rewrite (reflect_iff _ _ (is_vty_adt_none ty)).
  destruct (is_vty_adt ty); simpl; split; auto; discriminate.
Qed.

Lemma is_vty_adt_some {ty: vty} {m a vs}:
  is_vty_adt ty = Some (m, a, vs) ->
  ty = vty_cons (adt_name a) vs /\
  adt_in_mut a m /\
  mut_in_ctx m gamma.
Proof.
  unfold is_vty_adt; intros.
  destruct ty; try discriminate.
  destruct (find_ts_in_ctx t) eqn : Hfind; try discriminate.
  destruct p as [m' a']. inversion H; subst.
  apply find_ts_in_ctx_some in Hfind.
  destruct_all; subst; auto.
Qed.

(*First, a weaker spec that does not rely on
  the context being well-formed*)
(*
Lemma find_ts_in_ctx_weak (ts: typesym):
  reflect (exists (a: alg_datatype) (m: mut_adt),
    mut_in_ctx m gamma /\ adt_in_mut a m /\
    adt_name a = ts) (ssrbool.isSome (find_ts_in_ctx ts)).
Proof.
  destruct (find_ts_in_ctx ts) eqn : Hfind; simpl;
  [apply ReflectT | apply ReflectF].
  - destruct p as [m a]. apply find_ts_in_ctx_some in Hfind.
    destruct_all; subst. exists a. exists m. auto.
  - rewrite <- find_ts_in_ctx_none_iff in Hfind.
    intros [a [m [m_in [a_in Hts]]]]; subst.
    apply (Hfind a m); auto.
Qed. 

Lemma is_vty_adt_isSome ts tys:
  ssrbool.isSome (is_vty_adt (vty_cons ts tys)) =
  ssrbool.isSome (find_ts_in_ctx ts).
Proof.
  simpl. destruct (find_ts_in_ctx ts); simpl; auto.
  destruct p; auto.
Qed.*)

Lemma is_vty_adt_weak (ty: vty):
  reflect (exists (a: alg_datatype) (m: mut_adt) (args: list vty),
    mut_in_ctx m gamma /\ adt_in_mut a m /\ 
    ty = vty_cons (adt_name a) args) (ssrbool.isSome (is_vty_adt ty)).
Proof.
  destruct (is_vty_adt ty) eqn : Hadt; simpl; 
  [apply ReflectT | apply ReflectF].
  - destruct p as [[m a] vs].
    apply is_vty_adt_some in Hadt. destruct_all.
    exists a. exists m. exists vs. auto.
  - rewrite <- is_vty_adt_none_iff in Hadt.
    intros [a [m [vs [m_in [a_in Hty]]]]]; subst.
    apply (Hadt a m vs); auto.
Qed.

(*Now, the stronger specs*)
Context {sigma: sig} (gamma_valid: valid_context sigma gamma).


Lemma no_adt_name_dups:
  NoDup (map adt_name (concat (map typs (mut_of_context gamma)))).
Proof.
  assert (forall g, 
    (map adt_name (concat (map typs (mut_of_context g)))) =
  typesyms_of_context g). {
    induction g; unfold typesyms_of_context in *; simpl; auto.
    unfold datatypes_of_context in *.
    destruct a; simpl; auto.
    rewrite !map_app, IHg. f_equal.
    rewrite map_map.
    apply map_ext. intros a. destruct a; reflexivity.
  }
  rewrite H. apply gamma_valid.
Qed.

(*The real spec we want: *)
Lemma find_ts_in_ctx_iff: forall ts m a,
  (find_ts_in_ctx ts = Some (m, a) <-> mut_in_ctx m gamma /\
    adt_in_mut a m /\ adt_name a = ts).
Proof.
  intros. unfold find_ts_in_ctx. rewrite mut_in_ctx_eq.
  assert (forall m, In m (mut_of_context gamma) ->
    NoDup (map adt_name (typs m))). {
      intros m'. rewrite <- mut_in_ctx_eq.
      eapply adts_names_nodups. apply gamma_valid.
    }
  assert (Hnodup:=no_adt_name_dups).
  induction (mut_of_context gamma); simpl; intros; split; intros; auto.
  - inversion H0.
  - destruct H0 as [[] _].
  - destruct (find_ts_in_mut ts a0) eqn : Hmut.
    + inversion H0; subst. apply find_ts_in_mut_iff in Hmut. destruct Hmut.
      repeat split; auto.
      apply H. left; auto.
    + apply IHl in H0. destruct H0 as [Hin [Ha Hn]]. repeat split; auto.
      intros. apply H. right; auto.
      simpl in Hnodup. rewrite map_app in Hnodup. apply NoDup_app in Hnodup.
      apply Hnodup.
  - destruct H0 as [[Ham | Hinm] [Ha Hn]]; subst.
    + assert (find_ts_in_mut (adt_name a) m = Some a). {
        apply find_ts_in_mut_iff. apply H. left; auto. split; auto.
      }
      rewrite H0. reflexivity.
    + simpl in Hnodup. rewrite map_app in Hnodup.
      rewrite NoDup_app_iff in Hnodup.
      destruct (find_ts_in_mut (adt_name a) a0 ) eqn : Hf.
      * apply find_ts_in_mut_iff in Hf. 2: apply H; simpl; auto.
        destruct Hf.
        destruct Hnodup as [Hn1 [Hn2 [Hi1 Hi2]]].
        exfalso. apply (Hi1 (adt_name a1)). rewrite in_map_iff.
        exists a1. split; auto. apply (in_bool_In _ _ _ H0).
        rewrite H1.
        rewrite in_map_iff. exists a. split; auto.
        rewrite in_concat. exists (typs m). split; auto.
        rewrite in_map_iff. exists m; split; auto.
        (*TODO: automate this or at least fix lemma w args*)
        apply (in_bool_In _ _ _ Ha).
      * apply IHl; auto.
        intros. apply H. right; auto.
        apply Hnodup.
Qed.

Lemma is_vty_adt_iff {ty: vty} {m a vs}:
  is_vty_adt ty = Some (m, a, vs) <->
  ty = vty_cons (adt_name a) vs /\
  adt_in_mut a m /\
  mut_in_ctx m gamma.
Proof.
  unfold is_vty_adt. split.
  - destruct ty; intro C; inversion C.
    destruct (find_ts_in_ctx t) eqn : Hts; inversion H0; subst.
    destruct p. inversion C; subst.
    apply find_ts_in_ctx_iff in Hts. destruct_all; subst; auto.
  - intros. destruct_all; subst; simpl.
    assert (find_ts_in_ctx (adt_name a) = Some (m, a)). {
      apply find_ts_in_ctx_iff. split; auto.
    }
    rewrite H. reflexivity.
Qed.

(*NOTE: this is now [is_vty_adt_some]*)
(*
Lemma is_vty_adt_spec {ty: vty} {m a vs}:
  is_vty_adt ty = Some (m, a, vs) ->
  ty = vty_cons (adt_name a) vs /\
  adt_in_mut a m /\
  mut_in_ctx m gamma.
Proof.
  apply is_vty_adt_iff.
Qed.*)

Lemma adt_vty_length_eq: forall {ty m a vs},
  is_vty_adt ty = Some (m, a, vs) ->
  valid_type sigma ty ->
  length vs = length (m_params m).
Proof.
  intros ty m a vs H Hval.
  apply is_vty_adt_some in H. destruct_all; subst.
  inversion Hval; subst. rewrite H5.
  f_equal. apply (adt_args gamma_valid). split; auto.
Qed.

End GetADT.

(*TODO: will move, but this shows that we can actually
  write decreasing recursive functions*)

(*Let's do a quick test*)
(*Binary tree*)
Notation mk_fs name params args ret_ts ret_args := 
  (Build_funsym (Build_fpsym name params args eq_refl eq_refl) 
    (vty_cons ret_ts (map vty_var ret_args)) eq_refl).
Notation mk_ne l :=
  (list_to_ne_list l eq_refl).
    
Definition ta : typevar := "a"%string.
Definition ts_tree: typesym := mk_ts "tree" [ta].
Definition fs_leaf := mk_fs "Leaf" [ta] nil ts_tree [ta].
Definition fs_node := mk_fs "Node" [ta] 
[vty_var ta; vty_cons ts_tree [vty_var ta]; vty_cons ts_tree [vty_var ta]]
ts_tree [ta].

Definition tree_adt: alg_datatype :=
  alg_def ts_tree (mk_ne [fs_leaf; fs_node]).

Definition tree_mut : mut_adt :=
  (mk_mut [tree_adt] [ta] eq_refl).

(*Now we define the size function on ADTs*)

(*First, define the plus function symbol*)
Definition fs_plus := Build_funsym (Build_fpsym "plus" [ta] 
[vty_var ta; vty_var ta] eq_refl eq_refl) (vty_var ta) eq_refl.

(*Now we define the function symbol and the function body*)
Definition fs_size := Build_funsym (Build_fpsym "size" [ta]
  [vty_cons ts_tree [vty_var ta]] eq_refl eq_refl)
  (vty_var ta) eq_refl.

Definition tree_ty : vty := vty_cons ts_tree [vty_var ta].

Definition size_arg : vsymbol := ("t"%string, tree_ty).
Definition l_var : vsymbol := ("l"%string, tree_ty).
Definition r_var : vsymbol := ("r"%string, tree_ty).

Definition size_args : list vsymbol := [size_arg].

(*This is:
  match t with
  | Leaf => tm_d
  | Node t l r => Plus (size l) (size r)
  end*)
Definition size_body : term :=
  Tmatch (Tvar size_arg) (vty_cons ts_tree [vty_var ta])
    (*List of (pattern * term) pairs*)
    [ (Pconstr fs_leaf [vty_var ta] nil,
        (*Just return some garbage value*)
        tm_d
    );
    (Pconstr fs_node [vty_var ta] [Pvar size_arg; Pvar l_var; Pvar r_var],
      (*Make the recursive call*)
      Tfun fs_plus [vty_var ta] 
        [ Tfun fs_size [vty_var ta] [Tvar l_var];
          Tfun fs_size [vty_var ta] [Tvar r_var]]
    )
    ].

(*Now create the fs list*)
Definition size_sn : sn := mk_sn fs_size size_args 0 (*eq_refl eq_refl eq_refl*).
Definition size_fn : fn := mk_fn fs_size size_sn size_body (*eq_refl*).

Lemma size_decreases: decrease_fun [size_fn] nil nil
  (Some size_arg) tree_mut [vty_var ta] size_body.
Proof.
  unfold size_body.
  eapply Dec_tmatch with(a:=tree_adt).
  - left; auto.
  - unfold adt_in_mut. (*Well that is a problem, need computable*)
    apply In_in_bool. unfold tree_mut. simpl. left; auto.
  - reflexivity.
  - intros. simpl in H.
    destruct_all.
    + simpl. unfold tm_d.
      apply Dec_notin_t; simpl; intros; auto.
    + simpl. apply Dec_fun_notin.
      * simpl. intros [H | Hf]; auto. inversion H.
      * simpl; intros.
        destruct_all; simpl.
        -- (*This is the case with recursion*) 
          eapply Dec_fun_in with(f_decl:=size_fn)(x:=l_var); try
            reflexivity; simpl; auto.
        -- (*Other case*) 
          eapply Dec_fun_in with(f_decl:=size_fn)(x:=r_var); try
            reflexivity; simpl; auto.
        -- destruct H.
    + destruct H.
Qed.