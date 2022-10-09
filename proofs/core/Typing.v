Require Import Common.
Require Import Types.
Require Import Syntax.

(** Typechecking **)

(*Signature*)
Record sig :=
  {
    sig_t : list typesym;
    sig_f: list funsym;
    sig_p: list predsym
  }.

(* Typing rules for types *)

Inductive valid_type : sig -> vty -> Prop :=
  | vt_int: forall s,
    valid_type s vty_int
  | vt_real: forall s,
    valid_type s vty_real
  | vt_tycons: forall s ts vs,
    In ts (sig_t s) ->
    length vs = length (ts_args ts) ->
    (forall x, In x vs -> valid_type s x) ->
    (*Forall (fun x => valid_type s x) vs ->*)
    valid_type s (vty_cons ts vs).
(*Notation "s '|-' t" := (valid_type s t) (at level 40).*)

(*Typing rules for patterns*)
Inductive pattern_has_type: sig -> pattern -> vty -> Prop :=
  | P_Var: forall s x ty,
    valid_type s ty ->
    pattern_has_type s (Pvar x ty) ty
  | P_Wild: forall s ty,
    valid_type s ty ->
    pattern_has_type s Pwild ty
  | P_Constr: forall s (params : list vty) (ps : list pattern) (f: funsym),
    In f (sig_f s) ->
    Forall (valid_type s) params ->
    length ps = length (s_args f) ->
    length params = length (s_params f) ->
    (* For all i, [nth i tms] has type [sigma(nth i (s_args f))], where
      sigma is the type substitution that maps f's type vars to [params] *)
    let sigma : vty -> vty := ty_subst (s_params f) params in
    Forall (fun x => pattern_has_type s (fst x) (snd x)) (combine ps
      (map sigma (s_args f))) ->
    (* No free variables in common *)
    (forall i j d x, i < length ps -> j < length ps -> i <> j ->
      ~(In x (pat_fv (nth i ps d)) /\ In x (pat_fv (nth j ps d)))) ->
        pattern_has_type s (Pconstr f params ps) (sigma (s_ret f))
  | P_Or: forall s p1 p2 ty,
    pattern_has_type s p1 ty ->
    pattern_has_type s p2 ty ->
    (forall x, In x (pat_fv p1) <-> In x (pat_fv p2)) ->
    pattern_has_type s (Por p1 p2) ty
  | P_Bind: forall s x ty p,
    ~ In x (pat_fv p) ->
    pattern_has_type s p ty ->
    pattern_has_type s (Pvar x ty) ty.

(* Typing rules for terms *)
Inductive term_has_type: sig -> term -> vty -> Prop :=
  | T_int: forall s z,
    term_has_type s (Tconst (ConstInt z)) vty_int
  | T_real: forall s r,
    term_has_type s (Tconst (ConstReal r)) vty_real
  | T_Var: forall s x ty,
    valid_type s ty ->
    term_has_type s (Tvar x ty) ty
  | T_Fun: forall s (params : list vty) (tms : list term) (f: funsym),
    In f (sig_f s) ->
    Forall (valid_type s) params ->
    (*NOTE: NOT included in paper - is this implied elsewhere?*)
    valid_type s (s_ret f) ->
    length tms = length (s_args f) ->
    length params = length (s_params f) ->
    (* For all i, [nth i tms] has type [sigma(nth i (s_args f))], where
      sigma is the type substitution that maps f's type vars to [params] *)
    let sigma : vty -> vty := ty_subst (s_params f) params in
    Forall (fun x => term_has_type s (fst x) (snd x)) (combine tms
      (map (ty_subst (s_params f) params) (s_args f))) ->
    term_has_type s (Tfun f params tms) (ty_subst (s_params f) params (s_ret f))
  | T_Let: forall s t1 x ty t2 ty2,
    term_has_type s t1 ty ->
    term_has_type s t2 ty2 ->
    term_has_type s (Tlet t1 x ty t2) ty2
  | T_If: forall s f t1 t2 ty,
    valid_formula s f ->
    term_has_type s t1 ty ->
    term_has_type s t2 ty ->
    term_has_type s (Tif f t1 t2) ty
  | T_Match: forall s tm ty1 (ps: list (pattern * term)) ty2,
    (*we defer the check for algebraic datatypes or exhaustiveness until
      later, because we need an additional context*)
    term_has_type s tm ty1 ->
    (forall x, In x ps -> pattern_has_type s (fst x) ty1) ->
    (forall x, In x ps -> term_has_type s (snd x) ty2) ->
    (*Makes things MUCH simpler to include this - TODO: is this a problem?
    If not, need to prove by knowing that pattern matching exhaustive, so
    nonempty, so can take 1st element. But then we need a context
    and additional hypotheses in semantics.*)
    valid_type s ty2 ->
    term_has_type s (Tmatch tm ty1 ps) ty2


(* Typing rules for formulas *)
with valid_formula: sig -> formula -> Prop :=
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
  | F_Quant: forall s q x ty f,
    valid_type s ty ->
    valid_formula s f ->
    valid_formula s (Fquant q x ty f)
  | F_Pred: forall s (params: list vty) (tms: list term) (p: predsym),
    (*Very similar to function case*)
    In p (sig_p s) ->
    Forall (valid_type s) params ->
    length tms = length (p_args p) ->
    length params = length (p_params p) ->
    let sigma : vty -> vty := ty_subst (p_params p) params in
    Forall (fun x => term_has_type s (fst x) (snd x))
      (combine tms (map sigma (p_args p))) ->
    valid_formula s (Fpred p params tms)
  | F_Let: forall s t x ty f,
    term_has_type s t ty ->
    valid_formula s f ->
    valid_formula s (Flet t x ty f)
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
    term_has_type s tm ty ->
    Forall(fun x => pattern_has_type s (fst x) ty) ps ->
    Forall (fun x => valid_formula s (snd x)) ps ->
    valid_formula s (Fmatch tm ty ps).
(*
Notation "s '|-' t ':' ty" := (term_has_type s t ty) (at level 40).
Notation "s '|-' f" := (valid_formula s f) (at level 40).*)

Lemma bool_dec: forall {A: Type} (f: A -> bool),
  (forall x : A, {is_true (f x)} + {~ is_true (f x)}).
Proof.
  intros A f x. destruct (f x) eqn : Hfx; auto.
  right. intro C. inversion C.
Qed.

(* Let's try to build a typechecker *)
Fixpoint typecheck_type (s:sig) (v: vty) : bool :=
  match v with
  | vty_int => true
  | vty_real => true
  | vty_var tv => false
  | vty_cons ts vs => 
      In_dec typesym_eq_dec ts (sig_t s) &&
      Nat.eqb (length vs) (length (ts_args ts)) &&
      (fix check_list (l: list vty) : bool :=
      match l with
      | nil => true
      | x :: t => typecheck_type s x && check_list t
      end) vs
  end.

(*We would like to prove this correct*)
Lemma typecheck_type_correct: forall (s: sig) (v: vty),
  valid_type s v <-> typecheck_type s v = true.
Proof.
  intros s. induction v; simpl; try solve[split; auto; constructor].
  - split; intros Hty; inversion Hty.
  - split; intros Hty.
    + inversion Hty; subst. repeat(apply andb_true_intro; split).
      simpl_sumbool. apply Nat.eqb_eq. auto.
      clear Hty H2 H4. induction vs; simpl; auto; intros.
      inversion H; subst. rewrite <- Forall_forall in H5. inversion H5; subst.
      apply andb_true_intro; split; auto. apply H2; auto.
      apply IHvs; auto. apply Forall_forall. auto.
    + apply andb_true_iff in Hty; destruct Hty.
      apply andb_true_iff in H0; destruct H0.
      simpl_sumbool. apply Nat.eqb_eq in H2. constructor; auto.
      clear i H2. induction vs; simpl; auto; intros. inversion H0.
      apply andb_true_iff in H1; destruct H1.
      inversion H; subst. destruct H0; subst; auto.
      apply H5; auto.
Qed.

(*First, try this: TODO move*)
Lemma fun_ty_inversion: forall s (f: funsym) (vs: list vty) (tms: list term) ty_ret,
  term_has_type s (Tfun f vs tms) ty_ret ->
  In f (sig_f s) /\ Forall (valid_type s) vs /\
  length tms = length (s_args f) /\
  length vs = length (s_params f) /\
  Forall (fun x => term_has_type s (fst x) (snd x)) 
    (combine tms (map (ty_subst (s_params f) vs) (s_args f))) /\
  ty_ret = ty_subst (s_params f) vs (s_ret f).
Proof.
  intros. inversion H; subst; repeat split; auto.
Qed.

Lemma pred_ty_inversion: forall s (p: predsym) (vs: list vty) (tms: list term),
  valid_formula s (Fpred p vs tms) ->
  In p (sig_p s) /\ Forall (valid_type s) vs /\
  length tms = length (p_args p) /\
  length vs = length (p_params p) /\
  Forall (fun x => term_has_type s (fst x) (snd x)) 
    (combine tms (map (ty_subst (p_params p) vs) (p_args p))).
Proof.
  intros. inversion H; subst; repeat split; auto.
Qed.

Lemma valid_type_v_subst: forall s (f: typevar -> vty) (ty: vty),
  valid_type s ty ->
  (forall x, valid_type s (f x)) ->
  valid_type s (v_subst_aux f ty).
Proof.
  intros.
  induction H; simpl; constructor; auto.
  rewrite map_length. apply H1.
  intros x. rewrite in_map_iff. intros [x1 [Hx1 Hinx1]].
  specialize (H3 _ Hinx1 H0). subst. apply H3.
Qed.

(*TODO: use previous lemma to prove*)
Lemma valid_type_subst: forall s ty vars tys,
  valid_type s ty ->
  Forall (valid_type s) tys ->
  valid_type s (ty_subst vars tys ty).
Proof.
  intros. induction H; unfold ty_subst; simpl; constructor; auto.
  rewrite map_length. apply H1.
  intros x. rewrite in_map_iff. intros [x1 [Hx1 Hinx1]].
  specialize (H3 _ Hinx1 H0). subst. apply H3.
Qed. 



(* Well-formed signmatures and Contexts *)

(* A well-formed signature requires all types that appear in a function/predicate
  symbol to be well-typed and for all free type variables in these types to appear
  in the function/predicate type parameters*)
Definition wf_sig (s: sig) : Prop :=
  (*For function symbols:*)
  Forall (fun (f: funsym) =>
    Forall (fun (t: vty) => 
      valid_type s t /\ Forall (fun (fv: typevar) => In fv (s_params f)) (type_vars t)
    ) ((s_ret f) :: (s_args f))
  ) (sig_f s) /\
  (*Predicate symbols are quite similar*)
  Forall (fun (p: predsym) =>
    Forall (fun (t: vty) => 
      valid_type s t /\ Forall (fun (fv: typevar) => In fv (p_params p)) (type_vars t)
    ) (p_args p)
  ) (sig_p s).

(*A context includes definitions for some of the types/functions/predicates in
  a signature*)
Definition context := list def.

Definition datatypes_of_context (c: context) : list (typesym * list funsym) :=
  concat (map datatypes_of_def c).

Definition mut_of_context (c: context) : list mut_adt :=
  fold_right (fun x acc => match x with
    | datatype_def m => m :: acc
    | _ => acc
    end) nil c.

Definition mutrec_datatypes_of_context (c: context) : list (list (typesym * list funsym)) :=
  map datatypes_of_def c.

Definition fundefs_of_context (c: context) : list (funsym * list vsymbol * term) :=
  concat (map fundefs_of_def c).

Definition preddefs_of_context (c: context) : list (predsym * list vsymbol * formula) :=
  concat (map preddefs_of_def c).

Definition indpreds_of_context (c: context) : list (predsym * list formula) :=
  concat (map indpreds_of_def c).

Definition typesyms_of_context (c: context) : list typesym :=
  map fst (datatypes_of_context c).

Definition funsyms_of_context (c: context) : list funsym :=
  concat (map funsyms_of_def c).

Definition predsyms_of_context (c: context) : list predsym :=
  concat (map predsyms_of_def c).

(*Ways of dealing with adts and parts in context*)
Definition mut_in_ctx (m: mut_adt) (gamma: context) :=
  In (datatype_def m) gamma.

Lemma mut_in_ctx_eq: forall m gamma,
  mut_in_ctx m gamma <-> In m (mut_of_context gamma).
Proof.
  intros. unfold mut_of_context, mut_in_ctx.
  induction gamma; simpl; intros; auto.
  - reflexivity.
  - split; intros.
    + destruct H; subst; simpl; auto.
      apply IHgamma in H.
      destruct a; simpl; auto.
    + destruct a; simpl in H; try solve[right; apply IHgamma; auto].
      destruct H. left; subst; auto. right; apply IHgamma; auto.
Qed.

Definition mut_typs_in_ctx (l: list alg_datatype) (gamma: context) :=
  exists (vars: list typevar) (H: nodupb typevar_eq_dec vars), 
  In (datatype_def (mk_mut l vars H)) gamma.

Definition adt_in_mut (a: alg_datatype) (m: mut_adt) :=
  In a (typs m).

Definition ts_in_mut_list (ts: typesym) (m: list alg_datatype) : bool :=
  in_bool typesym_eq_dec ts (map adt_name m).


Lemma ts_in_mut_list_ex: forall ts m,
  ts_in_mut_list ts (typs m) -> { a | ts = adt_name a /\ 
  adt_in_mut a m}.
Proof.
  unfold adt_in_mut, ts_in_mut_list; intros. induction (typs m); simpl.
  - inversion H.
  - simpl in H.
    destruct (typesym_eq_dec ts (adt_name a)); subst.
    + apply (exist _ a). split; auto.
    + specialize (IHl H).
      destruct IHl as [a' [Ha' Hina']].
      apply (exist _ a'). subst; split; auto.
Qed.

Lemma ts_in_mut_list_spec: forall ts m,
  ts_in_mut_list ts (typs m) <-> exists a, ts = adt_name a /\ 
  adt_in_mut a m.
Proof.
  intros. unfold adt_in_mut, ts_in_mut_list. induction (typs m); simpl.
  - split; intros; auto. inversion H. destruct H as [a [_ []]].
  - split; intros.
    + destruct (typesym_eq_dec ts (adt_name a)).
      * subst. exists a. split; auto.
      * apply IHl in H. destruct H as [a' [Ha' Hina']].
        subst. exists a'. split; auto.
    + destruct H as [a' [Ha' Hina']]; subst.
      destruct Hina'; subst.
      * destruct (typesym_eq_dec (adt_name a') (adt_name a')); auto;
        contradiction.
      * apply orb_true_iff. right. apply IHl.
        exists a'. split; auto.
Qed.

Definition adt_mut_in_ctx (a: alg_datatype) (m: mut_adt) (gamma: context) :=
  adt_in_mut a m /\ mut_in_ctx m gamma.

Definition adt_in_ctx (a: alg_datatype) (gamma: context) :=
  exists (m: mut_adt), adt_mut_in_ctx a m gamma.

Definition constr_in_adt (c: funsym) (a: alg_datatype) :=
  in_bool_ne funsym_eq_dec c (adt_constrs a).

Definition constr_adt_mut_in_ctx (c: funsym) (a: alg_datatype) 
  (m: mut_adt) (gamma: context) :=
  constr_in_adt c a /\ adt_mut_in_ctx a m gamma.

Definition constr_adt_in_ctx (c: funsym) (a: alg_datatype) (gamma: context) :=
  constr_in_adt c a /\ adt_in_ctx a gamma.

(*We also require that all type variables in mutually recursive types
  are correct: all component types and constructors have the same
  parameters*)
Definition valid_mut_rec (m: mut_adt) : Prop :=
  Forall (fun a => (m_params m) = (ts_args (adt_name a)) /\
    Forall (fun f => (m_params m) = (s_params f)) 
      (ne_list_to_list (adt_constrs a))) (typs m).

(*A context gamma extending signature s is well-formed if all type, function, and
  predicate symbols in gamma appear in s, and none appear more than once*)
(*Note: we do not check the type/function/pred symbols within the terms and formulas
  in the definition - these will be checked for the validity check for each
  definition.*)
Definition wf_context (s: sig) (gamma: context) :=
  wf_sig s /\
  Forall (fun t => In t (sig_t s)) (typesyms_of_context gamma) /\
  Forall (fun f => In f (sig_f s)) (funsyms_of_context gamma) /\
  Forall (fun p => In p (sig_p s)) (predsyms_of_context gamma) /\
  NoDup (typesyms_of_context gamma) /\
  NoDup (funsyms_of_context gamma) /\
  NoDup (predsyms_of_context gamma).

(* Additional checks for pattern matches *)

(*In addition to what we have above, we also need to know that pattern
  matches operate on an algebraic data type and are exhaustive. We separate this
  check from the main typing relation for 2 reasons:
  1. The exhaustiveness check relies on well-typedness in a non-strictly-positive way
  2. This check depends on the context, as opposed to the typing relation, which only
    depends on the signature. *) 

Section MatchExhaustive.

Variable sigma: sig.
Variable gamma: context.

(*Describes when a pattern matches a term*)
Inductive matches : pattern -> term -> Prop :=
  | M_Var: forall v ty t,
    matches (Pvar v ty) t
  | M_Constr: forall (f: funsym) (vs: list vty) (ps: list pattern) (ts: list term),
    (forall x, In x (combine ps ts) -> matches (fst x) (snd x)) ->
    matches (Pconstr f vs ps) (Tfun f vs ts)
  | M_Wild: forall t,
    matches Pwild t
  | M_Or: forall p1 p2 t,
    matches p1 t \/ matches p2 t ->
    matches (Por p1 p2) t
  | M_Bind: forall p x ty t,
    matches p t ->
    matches (Pbind p x ty) t.

(*A match is exhaustive if for every instance of an alg_datatype,
  some pattern matches it*)
Definition exhaustive_match (a: alg_datatype) (args: list vty)
  (ps: list pattern) : Prop :=
  adt_in_ctx a gamma /\
  forall t, term_has_type sigma t (vty_cons (adt_name a) args) ->
    exists p, In p ps /\ matches p t.
  (*
  
  /\
  forall c, in_bool_ne funsym_eq_dec c (adt_constrs a) -> 

  forall (ts: list term), 
  term_has_type sigma (Tfun c args ts) (vty_cons (adt_name a) args) ->
  exists p, In p ps /\ matches p (Tfun c args ts).*)

(*A valid pattern match matches on a term of an ADT type and is exhaustive*)
Definition valid_pattern_match (*(t: term)*) (ps: list pattern) : Prop :=
  exists (a: alg_datatype) (args: list vty),
    length args = length (ts_args (adt_name a)) /\
    exhaustive_match a args ps.

(*We require that this recursively holds throughout the entire term/formula*)
Inductive valid_pat_tm : term -> Prop :=
  | VPT_const: forall c,
    valid_pat_tm (Tconst c)
  | VPT_var: forall v ty,
    valid_pat_tm (Tvar v ty)
  | VPT_fun: forall f vs ts,
    (forall x, In x ts -> valid_pat_tm x) ->
    valid_pat_tm (Tfun f vs ts)
  | VPT_let: forall t1 v ty t2,
    valid_pat_tm t1 ->
    valid_pat_tm t2 ->
    valid_pat_tm (Tlet t1 v ty t2)
  | VTY_if: forall f t1 t2,
    valid_pat_fmla f ->
    valid_pat_tm t1 ->
    valid_pat_tm t2 ->
    valid_pat_tm (Tif f t1 t2)
  | VTY_match: forall t ty (ps: list (pattern * term)),
    valid_pattern_match (map fst ps) ->
    (forall x, In x (map snd ps) -> valid_pat_tm x) ->
    valid_pat_tm (Tmatch t ty ps)
with valid_pat_fmla: formula -> Prop :=
  | VTF_pred: forall p vs ts,
    (forall x, In x ts -> valid_pat_tm x) ->
    valid_pat_fmla (Fpred p vs ts)
  | VTF_quant: forall q v ty f,
    valid_pat_fmla f ->
    valid_pat_fmla (Fquant q v ty f)
  | VTF_eq: forall ty t1 t2,
    valid_pat_tm t1 ->
    valid_pat_tm t2 ->
    valid_pat_fmla (Feq ty t1 t2)
  | VTF_binop: forall b f1 f2,
    valid_pat_fmla f1 ->
    valid_pat_fmla f2 ->
    valid_pat_fmla (Fbinop b f1 f2)
  | VTF_not: forall f,
    valid_pat_fmla f ->
    valid_pat_fmla (Fnot f)
  | VTF_true:
    valid_pat_fmla Ftrue
  | VTF_false:
    valid_pat_fmla Ffalse
  | VTF_let: forall t x ty f,
    valid_pat_tm t ->
    valid_pat_fmla f ->
    valid_pat_fmla (Flet t x ty f)
  | VTF_if: forall f1 f2 f3,
    valid_pat_fmla f1 ->
    valid_pat_fmla f2 ->
    valid_pat_fmla f3 ->
    valid_pat_fmla (Fif f1 f2 f3)
  | VTF_match: forall t ty (ps: list (pattern * formula)),
    valid_pattern_match (map fst ps) ->
    (forall x, In x (map snd ps) -> valid_pat_fmla x) ->
    valid_pat_fmla (Fmatch t ty ps).

End MatchExhaustive.

(*The full typing judgement for terms and formulas*)
Definition well_typed_term (s: sig) (gamma: context) (t: term) (ty: vty) : Prop :=
  term_has_type s t ty /\ valid_pat_tm s gamma t.

Definition well_typed_formula (s: sig) (gamma: context) (f: formula) : Prop :=
  valid_formula s f /\ valid_pat_fmla s gamma f.

(** Validity of definitions *)

(** Algebraic Data Types **)

(*For an algebraic datatype to be valid, the following must hold:
  1. All constructors must have the correct type and type parameters
  2. The type must be inhabited (there must be 1 constructor with
    only inhabited types)
  3. Instances of the type must appear in strictly positive positions *)

(*Types*)
(*All constructors have the correct return type and the same parameters as
  the declaration*)
Definition adt_valid_type (a : alg_datatype) : Prop :=
  match a with
  | alg_def ts constrs => 
    Forall (fun (c: funsym) => 
      (s_params c) = (ts_args ts) /\ 
      (s_ret c) = vty_cons ts (map vty_var (ts_args ts))) 
        (ne_list_to_list constrs)
  end.

(*Inhabited types*)
Section Inhab.

Variable s: sig.
Variable gamma: context.
Variable gamma_wf: wf_context s gamma.

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
    ~ In ts (sig_t s) ->
    typesym_inhab tss tvs ts false
  | ts_check_rec: forall tss tvs ts, (*recursive type*)
    In ts tss ->
    typesym_inhab tss tvs ts false
  | ts_check_typeT: forall tss tvs ts, (*for abstract type*)
    ~ In ts tss ->
    ~ In ts (map fst (datatypes_of_context gamma)) ->
    In ts (sig_t s) ->
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
    In ts (sig_t s) ->
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
  | constr_checkT: forall tss tvs c,
    (forall x, In x (s_args c) -> vty_inhab tss tvs x true) ->
    constr_inhab tss tvs c true
  | constr_checkF: forall tss tvs c v,
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
    (exists vs, (ty_subst params substs (s_ret T)) = vty_cons I vs /\
      (forall x v, In x ts -> In v vs -> negb (typesym_in x v))) ->
    nested_positive T params substs I ts.

Inductive positive : funsym -> list typesym -> Prop :=
  (*We combine into one case because of we don't have true function types*)
  | Pos_constr: forall (constr: funsym) (ts: list typesym),
    (forall vty, In vty (s_args constr) -> strictly_positive vty ts) ->
    (exists t vtys, In t ts /\ s_ret constr = vty_cons t vtys /\
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

(* Recursive Functions and Predicates *)
Section FunPredSym.

Variable s: sig.
Variable gamma: context.

(*A function/pred symbol is well-typed if the term has the correct return type of
  the function and all free variables in t are included in the arguments vars*)

Definition funpred_def_valid_type (fd: funpred_def) : Prop :=
  match fd with
  | fun_def f vars t =>
    well_typed_term s gamma t (s_ret f) /\
    sublist (term_fv t) vars
  | pred_def p vars f =>
    well_typed_formula s gamma f /\
    sublist (form_fv f) vars
  end.
  (*TODO: handle type vars? Do we need to, or is that handled by wf of f?*)

(*Termination*)

(*TODO*)

(*Inductive Predicates*)

(*Each clause must be a closed formula, well-typed, and belong to a restricted grammar, which
  we give both as an inductive definition and a computable Fixpoint below*)

Inductive valid_ind_form (p: predsym) : formula -> Prop :=
  | VI_pred: forall (tys : list vty) tms,
    tys = map vty_var (p_params p) ->
    length (p_args p) = length tms ->
    valid_ind_form p (Fpred p tys tms)
  | VI_impl: forall f1 f2,
    valid_ind_form p f2 ->
    valid_ind_form p (Fbinop Timplies f1 f2)
  | VI_forall: forall x ty f,
    valid_ind_form p f ->
    valid_ind_form p (Fquant Tforall x ty f)
  | VI_let: forall x ty t f,
    valid_ind_form p f ->
    valid_ind_form p (Flet t x ty f).
     
Fixpoint valid_ind_form_dec (p: predsym) (f: formula) : bool :=
  match f with
  | Fpred p' tys tms => predsym_eq_dec p p' && list_eq_dec vty_eq_dec tys (map vty_var (p_params p))
    && (length (p_args p) =? length tms)
  | Fquant Tforall x ty f' => valid_ind_form_dec p f'
  | Fbinop Timplies f1 f2 => valid_ind_form_dec p f2
  | Flet t x ty f' => valid_ind_form_dec p f'
  | _ => false
  end.

Lemma valid_ind_form_equiv: forall p f,
  reflect (valid_ind_form p f) (valid_ind_form_dec p f).
Proof.
  intros. apply iff_reflect. induction f using formula_ind with (P:=(fun _ => True)); auto; simpl;
  (split; [intros C;inversion C; subst| intros]); auto; try solve[intuition]; try solve[constructor];
  try match goal with | H: false = true |- _ => inversion H end.
  - rewrite H3, Nat.eqb_refl, andb_true_r. apply andb_true_intro; split; simpl_sumbool. 
  - repeat(apply andb_prop in H; destruct H). repeat simpl_sumbool. constructor; auto.
    apply Nat.eqb_eq. auto.
  - destruct q;[constructor; intuition |inversion H].
  - destruct b; try inversion H. constructor. intuition.
  - constructor. intuition.
Qed.

Definition indprop_valid_type (i: indpred_def) : Prop :=
  match i with
  | ind_def p lf => Forall (fun f => well_typed_formula s gamma f /\ 
      closed_formula f /\ valid_ind_form p f) lf
  end.

(*Strict Positivity*)

(*First, does a predicate symbol appear in a formula? Because of "if" expressions,
  we also need a version for terms*)
Fixpoint predsym_in (p: predsym) (f: formula) {struct f}  : bool :=
  match f with
  | Fpred ps tys tms => predsym_eq_dec p ps || existsb (predsym_in_term p) tms
  | Fquant q x ty f' => predsym_in p f'
  | Feq ty t1 t2 => predsym_in_term p t1 || predsym_in_term p t2
  | Fbinop b f1 f2 => predsym_in p f1 || predsym_in p f2
  | Fnot f' => predsym_in p f'
  | Ftrue => false
  | Ffalse => false
  | Flet t x ty f' => predsym_in_term p t || predsym_in p f'
  | Fif f1 f2 f3 => predsym_in p f1 || predsym_in p f2 || predsym_in p f3
  | Fmatch t ty ps => predsym_in_term p t || existsb (fun x => predsym_in p (snd x)) ps
  end
  
with predsym_in_term (p: predsym) (t: term) {struct t}  : bool :=
  match t with
  | Tconst _ => false
  | Tvar _ _ => false
  | Tfun fs tys tms => existsb (predsym_in_term p) tms
  | Tlet t1 x ty t2 => predsym_in_term p t1 || predsym_in_term p t2
  | Tif f t1 t2 => predsym_in p f || predsym_in_term p t1 || predsym_in_term p t2
  | Tmatch t ty ps => predsym_in_term p t || existsb (fun x => predsym_in_term p (snd x)) ps
  end.
  
(*Here, strict positivity is a bit simpler, because predicates are not
  higher-order; we only need to reason about implication, essentially *)

(*Inductive case and nested positivity cannot occur because we cannot
  take a predicate as an argument (ie: can't have list x, where x : Prop)*)
Inductive ind_strictly_positive (ps: list predsym) : formula -> Prop :=
  | ISP_notin: forall (f: formula),
    (forall p, In p ps -> negb (predsym_in p f)) ->
    ind_strictly_positive ps f
  | ISP_pred: forall (p: predsym) 
    (vs: list vty) (ts: list term),
    In p ps ->
    (forall x t, In t ts -> In x ps -> negb (predsym_in_term x t)) ->
    ind_strictly_positive ps (Fpred p vs ts)
  | ISP_impl: forall  (f1 f2: formula),
    ind_strictly_positive ps f2 ->
    (forall p, In p ps -> negb(predsym_in p f1)) ->
    ind_strictly_positive ps (Fbinop Timplies f1 f2)
  (*The rest of the cases are not too interesting*)
  | ISP_quant: forall (q: quant) (x: vsymbol) (ty: vty) (f: formula),
    ind_strictly_positive ps f ->
    ind_strictly_positive ps (Fquant q x ty f)
  | ISP_and: forall (f1 f2 : formula),
    ind_strictly_positive ps f1 ->
    ind_strictly_positive ps f2 ->
    ind_strictly_positive ps (Fbinop Tand f1 f2)
  | ISP_or: forall (f1 f2 : formula),
    ind_strictly_positive ps f1 ->
    ind_strictly_positive ps f2 ->
    ind_strictly_positive ps (Fbinop Tor f1 f2)
  | ISP_let: forall (t: term) (x: vsymbol) (ty: vty) (f: formula),
    (forall p, In p ps -> negb (predsym_in_term p t)) ->
    ind_strictly_positive ps f -> (*TODO: is this too restrictive as well? Think OK*)
    ind_strictly_positive ps (Flet t x ty f)
  | ISP_if: forall f1 f2 f3,
    (*Cannot be in guard because get (essentially), f1 -> f2 /\ ~f1 -> f3*)
    (forall p, In p ps -> negb(predsym_in p f1)) ->
    ind_strictly_positive ps f2 ->
    ind_strictly_positive ps f3 ->
    ind_strictly_positive ps (Fif f1 f2 f3)
  | ISP_match: forall (t: term) ty (pats: list (pattern * formula)),
    (forall p, In p ps -> negb (predsym_in_term p t)) ->
    (forall f, In f (map snd pats) -> ind_strictly_positive ps f) ->
    ind_strictly_positive ps (Fmatch t ty pats) 
  (*eq, not, iff covered by case "notin" - these cannot have even strictly
    positive occurrences *).


Inductive ind_positive (ps: list predsym) : formula -> Prop :=
  | IP_pred: forall (p: predsym) 
    (vs: list vty) (ts: list term),
    In p ps ->
    (forall x t, In t ts -> In x ps -> negb (predsym_in_term x t)) ->
    ind_positive ps (Fpred p vs ts)
  | IP_forall: forall (x: vsymbol) (ty: vty) (f: formula),
    ind_positive ps f ->
    (* Don't need strict positivity for ty because we cannot quantify over formulas*)
    ind_positive ps (Fquant Tforall x ty f)
  | IP_let: forall (t: term) (x: vsymbol) (ty: vty) (f: formula),
    (*TODO: is this the right condition? I think so, but should we allow this
      symbol to appear in terms in any cases?*)
    (forall p, In p ps -> negb (predsym_in_term p t)) ->
    ind_positive ps f ->
    ind_positive ps (Flet t x ty f)
  | IP_impl: forall (f1 f2: formula),
    ind_strictly_positive ps f1 ->
    ind_positive ps f2 ->
    ind_positive ps (Fbinop Timplies f1 f2).

Definition indpred_positive (l: list indpred_def) : Prop :=
  let ps : list predsym :=
    map (fun i => match i with |ind_def p fs => p end) l in
  let fs: list formula :=
    concat (map (fun i => match i with |ind_def p fs => fs end) l) in
  Forall (ind_positive ps) fs.

End FunPredSym.

(*Put it all together*)
Definition valid_context (s : sig) (gamma: context) :=
  wf_context s gamma /\
  Forall (fun d =>
    match d with
    | datatype_def m => Forall adt_valid_type (typs m) /\ 
                           Forall (adt_inhab s gamma) (typs m) /\
                           adt_positive gamma (typs m) /\
                           valid_mut_rec m
    | recursive_def fs => Forall (funpred_def_valid_type s gamma) fs
    | inductive_def is => Forall (indprop_valid_type s gamma) is /\
                          indpred_positive is
    end) gamma.

Lemma wf_context_expand: forall s d gamma,
  wf_context s (d :: gamma) ->
  wf_context s gamma.
Proof.
  intros s d gamma. unfold wf_context. intros.
  unfold typesyms_of_context, datatypes_of_context, 
  funsyms_of_context, predsyms_of_context in *; 
  simpl in *; rewrite map_app in *.
  repeat match goal with
  | H: ?P /\ ?Q |- _ => destruct H
  | H: Forall ?P (?l1 ++ ?l2) |- _ => apply Forall_app in H
  | H: NoDup (?l1 ++ ?l2) |- _ => apply NoDup_app in H
  | |- ?P /\ ?Q => split; auto
  end.
Qed.

Section ValidContextLemmas.

Context {s: sig} {gamma: context} (gamma_valid: valid_context s gamma).

(*These lemmas all have the same form: keep applying Forall_forall, in_map_iff,
  and similar, until we get what we want. Here we automate them*)
Ltac valid_context_tac :=
  let Hwf := fresh "Hwf" in
  let Hadts := fresh "Hadts" in
  destruct gamma_valid as [Hwf Hadts];
  rewrite Forall_forall in Hadts;
  unfold mut_in_ctx, adt_in_mut, constr_in_adt in *;
  repeat match goal with
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
  end; auto.

(*
(a: typesym) (constrs: list funsym) (c: funsym),
  In (a, constrs) (datatypes_of_context gamma) ->
  In c constrs ->
  s_ret c = vty_cons a (map vty_var (ts_args a)) /\
  s_params c = ts_args a.
Proof.
  intros. valid_context_tac.
  unfold adt_valid_type in H.
  valid_context_tac.
Qed.

Lemma adt_constr_ret_params_eq: forall {a: typesym} {constrs: list funsym} {c1 c2: funsym},
  In (a, constrs) (datatypes_of_context gamma) ->
  In c1 constrs -> In c2 constrs ->
  s_ret c1 = s_ret c2 /\ s_params c1 = s_params c2.
Proof.
  intros.
  pose proof (adt_constr_ret_params _ _ _ H H0).
  pose proof (adt_constr_ret_params _ _ _ H H1).
  destruct H2; destruct H3; split; congruence.
Qed.*)

(*TODO: automate this: just a bunch of Forall_forall, in_map_iff, etc*)
(*
Definition args_params_eq: forall {l: list (typesym * list funsym)}
  {c: funsym} {adt: typesym} {constrs: list funsym}
  (Hin1: In l (mutrec_datatypes_of_context gamma))
  (Hin2: In (adt, constrs) l)
  (Hin3: In c constrs),
  ts_args adt = s_params c.
Proof.
  intros. valid_context_tac.
  unfold adt_valid_type in H.
  valid_context_tac.
Qed.
*)
Lemma adt_args: forall {m: mut_adt} {a: alg_datatype}
  (Hin: adt_mut_in_ctx a m gamma),
  ts_args (adt_name a) = m_params m.
Proof.
  intros. unfold adt_mut_in_ctx in Hin. destruct Hin.
  unfold adt_in_mut in H. unfold mut_in_ctx in H0.
  valid_context_tac.
  unfold valid_mut_rec in H3.
  valid_context_tac.
Qed.

Lemma adt_constr_params: forall {m: mut_adt} {a: alg_datatype}
  {c: funsym} (Hm: mut_in_ctx m gamma)
  (Ha: adt_in_mut a m)
  (Hc: constr_in_adt c a),
  s_params c = m_params m.
Proof.
  intros. unfold mut_in_ctx in Hm. unfold adt_in_mut in Ha.
  unfold constr_in_adt in Hc.
  valid_context_tac.
  unfold valid_mut_rec in H2.
  valid_context_tac. rewrite <- H3. reflexivity.
  rewrite in_bool_ne_equiv in Hc.
  apply (reflect_iff _ _ (in_bool_spec funsym_eq_dec _ _)).
  apply Hc.
Qed.

Lemma adt_constr_ret: forall {m: mut_adt} {a: alg_datatype}
  {c: funsym} (Hm: mut_in_ctx m gamma) (Ha: adt_in_mut a m) 
  (Hc: constr_in_adt c a),
  s_ret c = vty_cons (adt_name a) (map vty_var (m_params m)).
Proof.
  intros.
  (*This is an ugly hack, should change tactic so it leaves "in"
  assumptions*)
  assert (adt_mut_in_ctx a m gamma) by 
    (unfold adt_mut_in_ctx; split; assumption). 
  valid_context_tac.
  unfold adt_valid_type in H0.
  rewrite in_bool_ne_equiv in Hc.
  apply (reflect_iff _ _ (in_bool_spec funsym_eq_dec _ _)) in Hc.
  valid_context_tac.
  rewrite H4. f_equal.
  f_equal. replace t with (adt_name ((alg_def t n))) by auto.
  apply adt_args. auto.
Qed. 

Lemma adts_names_nodups: forall {m: mut_adt}
  (Hin: mut_in_ctx m gamma),
  NoDup (map adt_name (typs m)).
Proof.
  intros. unfold mut_in_ctx in Hin.
  unfold valid_context in gamma_valid.
  destruct gamma_valid as [Hwf _].
  unfold wf_context in Hwf.
  clear -Hin Hwf.
  destruct Hwf as [_ [_ [_ [_ [Huniq _]]]]].
  induction gamma.
  - inversion Hin.
  - simpl in *. unfold typesyms_of_context in *.
    unfold datatypes_of_context in *. simpl in Huniq.
    rewrite map_app in Huniq.
    rewrite NoDup_app_iff in Huniq.
    destruct Huniq as [Hn1 [Hn2 [Hi1 Hi2]]].
    destruct Hin; subst.
    + simpl in Hn1. rewrite map_map in Hn1.
      unfold adt_name. 
      assert (forall {A} (l1 l2: list A), NoDup l1 -> l1 = l2
      -> NoDup l2) by (intros; subst; auto).
      apply (H _ _ _ Hn1).
      apply map_ext. intros. destruct a; reflexivity.
    + apply IHc. apply H. apply Hn2.
Qed.

Lemma adts_nodups: forall {m: mut_adt}
  (Hin: mut_in_ctx m gamma),
  NoDup (typs m).
Proof.
  intros.
  eapply NoDup_map_inv. apply adts_names_nodups. apply Hin.
Qed.

(*TODO: don't need these anymore but maybe useful later?*)

Lemma NoDup_equiv: forall {A: Type} (l: list A),
  NoDup l <-> (forall n1 n2 d1 d2, n1 < length l -> n2 < length l ->
    nth n1 l d1 = nth n2 l d2 -> n1 = n2).
Proof.
  intros A l. induction l; simpl; split; intros.
  - inversion H0.
  - constructor.
  - inversion H; subst.
    destruct n1.
    + destruct n2; auto.
      exfalso. apply H5. subst. apply nth_In. lia.
    + destruct n2. 
      * exfalso. apply H5. subst. apply nth_In. lia.
      * f_equal. rewrite IHl in H6.
        apply (H6 _ _ d1 d2); auto; lia.
  - constructor.
    + intro C.
      pose proof (In_nth l a a C).
      destruct H0 as [n [Hn Ha]].
      assert (0 = S n). {
        apply (H _ _ a a); try lia.
        auto.
      }
      inversion H0.
    + apply IHl. intros n1 n2 d1 d2 Hn1 Hn2 Heq.
      assert (S n1 = S n2). {
        apply (H _ _ d1 d2); try lia; auto.
      }
      inversion H0; auto.
Qed.
(*
Lemma nth_concat: forall {A: Type} {l: list (list A)} {l2: list A} 
{n: nat}
  {d} {n2 d2},
  n2 < length l ->
  n < length (concat l) ->
  nth n2 l d2 = l2 ->
  nth n (concat l) d =
    nth (n - length (concat (firstn n2 l))) l2 d.
Proof.
  intros A l; induction l; simpl; intros.
  - inversion H0.
  - destruct n2.
    + subst. simpl. 
  
  
  destruct H0.
  - induction l
*)

Lemma NoDup_not_cons: forall {A: Type} 
(eq_dec: forall (x y : A), {x = y} + {x <> y}) {a : A} {l},
  ~ NoDup (a :: l) <-> In a l \/ ~NoDup l.
Proof.
  intros.
  rewrite (reflect_iff _ _ (nodup_NoDup eq_dec _)).
  rewrite nodupb_cons.
  rewrite (reflect_iff _ _ (nodup_NoDup eq_dec _)).
  rewrite (reflect_iff _ _ (in_bool_spec eq_dec _ _)).
  split; intros; auto.
  - destruct (in_bool eq_dec a l); simpl. left; auto.
    simpl in H. right; auto.
  - destruct H.
    + rewrite H. simpl; intro C; inversion C.
    + intro C. destruct (nodupb eq_dec l). contradiction.
      rewrite andb_false_r in C. inversion C.
Qed. 

Lemma in_exists: forall {A: Type} {x: A} {l: list A},
  In x l <-> exists l1 l2, l = l1 ++ [x] ++ l2.
Proof.
  intros; induction l; simpl; split; intros.
  - destruct H.
  - destruct H as [l1 [l2 Hl]]. destruct l1; inversion Hl.
  - destruct H; subst.
    + exists nil. exists l. reflexivity.
    + apply IHl in H. destruct H as [l1 [l2 Hl]]; rewrite Hl.
      exists (a :: l1). exists l2. reflexivity.
  - destruct H as [l1 [l2 Hl]]; subst.
    destruct l1.
    + inversion Hl; subst. left; auto.
    + simpl in Hl. inversion Hl; subst.
      right. apply IHl. exists l1. exists l2. reflexivity.
Qed.

Lemma not_NoDup: forall {A: Type}
(eq_dec: forall (x y : A), {x = y} + {x <> y})
  (l: list A),
  ~NoDup l <->
  exists x l1 l2 l3,
    l = l1 ++ [x] ++ l2 ++ [x] ++ l3.
Proof.
  intros A eq_dec l; induction l; simpl; intros; split; intros.
  - exfalso. apply H. constructor.
  - intro C. destruct H as [x [l1 [l2 [l3 Hl]]]]; subst.
    destruct l1; inversion Hl.
  - apply (NoDup_not_cons eq_dec) in H.
    destruct H.
    + exists a. exists nil.
      apply in_exists in H. destruct H as [l1 [l2 Hl]].
      rewrite Hl. exists l1. exists l2. reflexivity.
    + apply IHl in H. destruct H as [x [l1 [l2 [l3 Hl]]]].
      rewrite Hl. exists x. exists (a :: l1). exists l2. exists l3.
      reflexivity.
  - rewrite NoDup_not_cons by apply eq_dec.
    destruct H as [x [l1 [l2 [l3 Hl]]]]. destruct l1.
    + inversion Hl; subst. left. apply in_or_app. right. left; auto.
    + inversion Hl; subst.
      right. apply IHl. exists x. exists l1. exists l2. exists l3.
      reflexivity.
Qed.

(*Just need these*)

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

(*awful hack - TODO fix*)
Definition mut_in_ctx' := mut_in_ctx.

Lemma constrs_nodups: forall {m: mut_adt} {constrs: ne_list funsym}
  {m_in: mut_in_ctx m gamma}
  (Hin: In constrs (map adt_constrs (typs m))),
  nodupb funsym_eq_dec (ne_list_to_list constrs).
Proof.
  intros. unfold mut_in_ctx in m_in.
  apply (reflect_iff _ _ (nodup_NoDup _ _)).
  rewrite in_map_iff in Hin. destruct Hin as [a [Ha Hina]]; subst.
  assert (m_in': mut_in_ctx' m gamma) by auto.
  valid_context_tac.
  unfold wf_context in Hwf. destruct Hwf as [_ [_ [_ [_ [_ [Hnodup _]]]]]].
  clear Hadts. unfold funsyms_of_context in Hnodup.
  assert (exists l l', In l (map funsyms_of_def gamma) /\ l = concat l' /\
    In (ne_list_to_list (adt_constrs a)) l'). {
      unfold funsyms_of_def. unfold adt_constrs.
      exists (concat
      (map
         (fun a0 : alg_datatype =>
          match a0 with
          | alg_def _ fs => ne_list_to_list fs
          end) (typs m))).
    exists ((map
    (fun a0 : alg_datatype =>
     match a0 with
     | alg_def _ fs => ne_list_to_list fs
     end) (typs m))).
      split; auto.
      - rewrite in_map_iff. exists (datatype_def m).
        split; auto.
      - split; auto. rewrite in_map_iff.
        exists a. split; auto. destruct a; reflexivity.
  }
  destruct H3 as [l [l' [Hinl [Hl Hinl']]]]; subst.
  eapply NoDup_concat'. apply funsym_eq_dec. 
  3: apply Hinl'. 2: apply Hinl.
  apply Hnodup.
Qed.

(*We want to know: when we have a valid context, a list of
  patterns in a valid match is nonempty*)

  (*TODO: we need to do this when we have a valid context, so that we
    know that mut adt is nonempty
    TODO: change to NOT datatypes_of_context*)
(*
Lemma valid_pattern_match_nil: forall s gamma,
  valid_context s gamma ->
  ~ valid_pattern_match s gamma nil.
Proof.
  clear gamma_valid s gamma.
  intros s gamma gamma_valid. intro C. unfold valid_pattern_match in C.
  destruct C as [a [args [Hlen [Hina Hex]]]].
  assert (adt_inhab s gamma a). {
    unfold adt_in_ctx in Hina. destruct Hina as [m Hm].
    unfold adt_mut_in_ctx, adt_in_mut, mut_in_ctx in Hm.
    valid_context_tac.
  }
  assert (Hinhab:=H).
  unfold adt_inhab in H. destruct a. 
  apply adt_inhab_inhab with (vs:=args) in Hinhab; auto.
  2 : { apply gamma_valid. }
  destruct Hinhab as [tm Htm].
  specialize (Hex tm Htm). destruct Hex as [p [[] _]].
Qed.*)

(*If a term has a type, that type is well-formed. We need the 
  [valid_pat_fmla] or else we could have an empty pattern*)
Lemma has_type_valid: forall (*s gamma*) t ty,
  (*well_typed_term s gamma t ty ->*)
  term_has_type s t ty ->
  valid_type s ty.
Proof.
  intros. induction H; try solve[constructor]; try assumption; auto.
  apply valid_type_subst; assumption.
Qed.
(*
  - inversion H0; subst. auto.
  - inversion H0; subst; auto.
  - inversion H0; subst.
    destruct ps.
    simpl in H6. exfalso. apply (valid_pattern_match_nil _ _ gamma_valid H6).
    simpl in H8. assert (valid_pat_tm s gamma (snd p)).
      apply H8. left. auto.
    apply (H3 p). left; auto. assumption. apply H8; left; auto.
Qed.*)

(*TODO: move*)
Lemma in_bool_ne_In {A: Set} (eq_dec: forall (x y : A), {x = y} + {x <> y})
  (x: A) (l: ne_list A):
  in_bool_ne eq_dec x l ->
  In x (ne_list_to_list l).
Proof.
  rewrite in_bool_ne_equiv. intros.
  apply (reflect_iff _ _ (in_bool_spec eq_dec x _)).
  assumption.
Qed.
  
(*All constrs are in [funsym_of_context gamma]*)
Lemma constrs_in_funsyms: forall {gamma c a m},
  mut_in_ctx m gamma ->
  adt_in_mut a m ->
  constr_in_adt c a ->
  In c (funsyms_of_context gamma).
Proof.
  clear.
  intros gamma c a m. unfold mut_in_ctx, adt_in_mut, constr_in_adt.
  intros m_in a_in c_in; induction gamma; simpl. inversion m_in.
  simpl in m_in. unfold funsyms_of_context in *. simpl.
  destruct m_in as [Ha0 | m_in]; [| apply in_or_app; right; auto].
  subst. apply in_or_app; left. simpl.
  rewrite in_concat. exists (ne_list_to_list (adt_constrs a)).
  rewrite in_map_iff. split; [| eapply in_bool_ne_In; apply c_in].
  exists a. split; auto. destruct a. reflexivity.
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

End ValidContextLemmas.