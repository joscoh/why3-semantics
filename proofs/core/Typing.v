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
    length tms = length (s_args f) ->
    length params = length (s_params f) ->
    (* For all i, [nth i tms] has type [sigma(nth i (s_args f))], where
      sigma is the type substitution that maps f's type vars to [params] *)
    let sigma : vty -> vty := ty_subst (s_params f) params in
    Forall (fun x => term_has_type s (fst x) (snd x)) (combine tms
      (map (ty_subst (s_params f) params) (s_args f))) ->
    term_has_type s (Tfun f params tms) (s_ret f)
  | T_Let: forall s t1 x ty t2 ty2,
    term_has_type s t1 ty ->
    term_has_type s t2 ty2 ->
    term_has_type s (Tlet t1 x ty t2) ty2
    (*TODO: make sure this works with nats as vars*)
  | T_If: forall s f t1 t2 ty,
    valid_formula s f ->
    term_has_type s t1 ty ->
    term_has_type s t2 ty ->
    term_has_type s (Tif f t1 t2) ty
  | T_Match: forall s tm ty1 (ps: list (pattern * term)) ty2,
    (*we defer the check for algebraic datatypes or exhaustiveness until
      later, because we need an additional context*)
    term_has_type s tm ty1 ->
    Forall (fun x => pattern_has_type s (fst x) ty1) ps ->
    Forall (fun x => term_has_type s (snd x) ty2) ps ->
    term_has_type s (Tmatch tm ps) ty2


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
    valid_formula s (Fmatch tm ps).
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
(*
Fixpoint typecheck_term (t: term) : option vty :=
  match t with
  | Tconst (ConstInt _) => Some vty_int
  | Tconst (ConstReal _) => Some vty_real
  | Tconst _ => None (*for now*)
  | Tvar n v => if typecheck_type v then Some v else None
  (*TODO: later*)
*)

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

(*A context gamma extending signature s is well-formed if all type, function, and
  predicate symbols in gamma appear in s, and none appear more than once*)
(*Note: we do not check the type/function/pred symbols within the terms and formulas
  in the definition - these will be checked for the validity check for each
  definition.*)
Definition wf_context (s: sig) (gamma: context) :=
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

Definition exhaustive_match (a: typesym) (constrs: list funsym) (args: list vty)
  (ps: list pattern) : Prop :=
  In (a, constrs) (datatypes_of_context gamma) /\
  forall c, In c constrs -> forall (ts: list term), 
  term_has_type sigma (Tfun c args ts) (vty_cons a args) ->
  exists p, In p ps /\ matches p (Tfun c args ts).

(*A valid pattern match matches on a term of an ADT type and is exhaustive*)
Definition valid_pattern_match (t: term) (ps: list pattern) : Prop :=
  exists (a: typesym) (args: list vty) (constrs: list funsym),
    exhaustive_match a constrs args ps.

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
  | VTY_match: forall t (ps: list (pattern * term)),
    valid_pattern_match t (map fst ps) ->
    (forall x, In x (map snd ps) -> valid_pat_tm x) ->
    valid_pat_tm (Tmatch t ps)
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
  | VTF_match: forall t (ps: list (pattern * formula)),
    valid_pattern_match t (map fst ps) ->
    (forall x, In x (map snd ps) -> valid_pat_fmla x) ->
    valid_pat_fmla (Fmatch t ps).

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
      (s_params c) = (ts_args ts) /\ (s_ret c) = vty_cons ts (map vty_var (ts_args ts))) constrs
  end.

(*Inhabited types*)
Section Inhab.

Variable s: sig.
Variable gamma: context.

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
  | ts_check_adtT: forall tss tvs ts constrs, (*for ADTs*)
    ~In ts tss ->
    In (ts, constrs) (datatypes_of_context gamma) ->
    negb (null constrs) ->
    (exists c, In c constrs /\ constr_inhab (ts :: tss) tvs c true) ->
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
  | constr_checkF: forall tss tvs c,
    (exists x, In x (s_args c) /\ vty_inhab tss tvs x false) ->
    constr_inhab tss tvs c false
(*Here, need bool to deal with strict positivity issues*)
with vty_inhab: list typesym -> list typevar -> vty -> bool -> Prop :=
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
    (forall x y, In (x, y) (combine (ts_args ts) args) ->
    ~ (In x new_tvs) -> vty_inhab tss tvs y true) ->
    (forall x y, In (x, y) (combine (ts_args ts) args) ->
      In x new_tvs -> vty_inhab tss tvs y false) ->
    typesym_inhab tss new_tvs ts true ->
    vty_inhab tss tvs (vty_cons ts args) true
  | vty_check_consF: forall tss tvs new_tvs ts args,
    (forall x y, In (x, y) (combine (ts_args ts) args) ->
    ~ (In x new_tvs) -> vty_inhab tss tvs y true) ->
    (forall x y, In (x, y) (combine (ts_args ts) args) ->
      In x new_tvs -> vty_inhab tss tvs y false) ->
    typesym_inhab tss new_tvs ts false ->
    vty_inhab tss tvs (vty_cons ts args) false
    .

(*An ADT is inhabited if its typesym is inhabited under the empty context*)
Definition adt_inhab (a : alg_datatype) : Prop :=
  match a with
  | alg_def ts constrs => typesym_inhab nil nil ts true
  end.

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
    we don't have built in function types - TODO: how to handle function types?
    should we add function types? Then we need application and lambdas*)
  | Strict_ind: forall (t: vty) (ts: list typesym) (I: typesym) 
    (constrs: list funsym) (vs: list vty),
    In (datatype_def [alg_def I constrs]) gamma -> (*singleton list means non-mutually recursive*)
    t = vty_cons I vs ->
    (forall (x: typesym) (v: vty), In x ts -> In v vs ->
      negb (typesym_in x v)) ->
    (forall (c: funsym), In c constrs ->
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
    concat (map (fun a => match a with | alg_def _ constrs => constrs end) l) in
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
    tys = map vty_var (p_params p) -> (*TODO: is this correct? All predsyms should have same type params, right?*)
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
  | Fmatch t ps => predsym_in_term p t || existsb (fun x => predsym_in p (snd x)) ps
  end
  
with predsym_in_term (p: predsym) (t: term) {struct t}  : bool :=
  match t with
  | Tconst _ => false
  | Tvar _ _ => false
  | Tfun fs tys tms => existsb (predsym_in_term p) tms
  | Tlet t1 x ty t2 => predsym_in_term p t1 || predsym_in_term p t2
  | Tif f t1 t2 => predsym_in p f || predsym_in_term p t1 || predsym_in_term p t2
  | Tmatch t ps => predsym_in_term p t || existsb (fun x => predsym_in_term p (snd x)) ps
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
  | ISP_match: forall (t: term) (pats: list (pattern * formula)),
    (forall p, In p ps -> negb (predsym_in_term p t)) ->
    (forall f, In f (map snd pats) -> ind_strictly_positive ps f) ->
    ind_strictly_positive ps (Fmatch t pats) 
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
    | datatype_def adts => Forall adt_valid_type adts /\ 
                           Forall (adt_inhab s gamma) adts /\
                           adt_positive gamma adts
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

Variable s: sig.
Variable gamma: context.
Variable gamma_valid: valid_context s gamma.

Lemma adt_constr_ret_params: forall  (a: typesym) (constrs: list funsym) (c: funsym),
  In (a, constrs) (datatypes_of_context gamma) ->
  In c constrs ->
  s_ret c = vty_cons a (map vty_var (ts_args a)) /\
  s_params c = ts_args a.
Proof.
  intros. unfold valid_context in gamma_valid.
  destruct gamma_valid.
  unfold datatypes_of_context in H.
  rewrite in_concat in H. destruct H as [datatyps [Hdatatyps Ha]].
  rewrite Forall_forall in H2. rewrite in_map_iff in Hdatatyps.
  destruct Hdatatyps as [d [Hd Hind]]; subst.
  specialize (H2 _ Hind). destruct d; simpl in Ha; try solve[inversion Ha].
  rewrite in_map_iff in Ha. destruct Ha as [alg [Halg Hinalg]].
  destruct alg as [ts fs]; inversion Halg; subst.
  rewrite Forall_forall in H2. apply H2 in Hinalg.
  unfold adt_valid_type in Hinalg.
  rewrite Forall_forall in Hinalg. apply Hinalg in H0. split; apply H0.
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
Qed.

End ValidContextLemmas.

