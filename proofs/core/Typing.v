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

(*First, we give a function version of this*)
(*Give fuel for termination*)
(*This is a terrible definition because we need to convince Coq that it terminates.
So we need lots of manual "fix" rather than existsb, forallb, fold_right, etc*)
Fixpoint typesym_inhab_fun (ninhab_vars: list typevar)
(seen_typesyms : list typesym) (ts: typesym) (n: nat) : bool :=
match n with
| O => false
| S(n') =>
  in_dec typesym_eq_dec ts (sig_t s) && 
  negb (in_dec typesym_eq_dec ts seen_typesyms) &&
  match (find_constrs gamma ts) with
  | None => null ninhab_vars
  | Some constrs => negb (null constrs) && 
    (fix exists_constr (l: list funsym) : bool :=
      match l with
      | nil => false
      | c :: tl => 
        ((fix forall_ty (lt: list vty) : bool :=
          match lt with
          | nil => true
          | t :: ttl =>
            ((fix check_type (t: vty) : bool :=
              match t with
              | vty_int => true
              | vty_real => true
              | vty_var v => negb (in_dec typevar_eq_dec v ninhab_vars)
              | vty_cons ts' vtys =>
                let bvars : list typevar :=
                  ((fix bad_vars (lvty: list vty) (lsym: list typevar) : list typevar :=
                  match lvty, lsym with
                  | x1 :: t1, x2 :: t2 => if check_type x1 then bad_vars t1 t2 else
                    x2 :: bad_vars t1 t2
                  | _, _ => nil
                  end) vtys (ts_args ts'))
                in
                typesym_inhab_fun bvars (ts :: seen_typesyms) ts' n'
              end) t) && forall_ty ttl
          end) (s_args c)) || (exists_constr tl)
      end) constrs
    end
  end.

(*We didn't want to write it with mutual recursion, but we can simplify now:*)
Fixpoint vty_inhab_fun (ninhab_vars: list typevar)
(seen_typesyms : list typesym) (t: vty) (n: nat) :=
match t with
| vty_int => true
| vty_real => true
| vty_var v => negb (in_dec typevar_eq_dec v ninhab_vars)
| vty_cons ts' vtys =>
    let bvars : list typevar :=
    ((fix bad_vars (lvty: list vty) (lsym: list typevar) : list typevar :=
    match lvty, lsym with
    | nil, nil => nil
    | x1 :: t1, x2 :: t2 => if vty_inhab_fun ninhab_vars seen_typesyms x1 n 
      then bad_vars t1 t2 else x2 :: bad_vars t1 t2
    | _, _ => nil
    end) vtys (ts_args ts')) in
  typesym_inhab_fun bvars (seen_typesyms) ts' n
end.

Fixpoint bad_vars (lvty: list vty) (lsym: list typevar) (f: vty -> bool) : list typevar :=
  match lvty, lsym with
  | x1 :: t1, x2 :: t2 => if f x1 then bad_vars t1 t2 f else
    x2 :: bad_vars t1 t2 f
  | _, _ => nil
  end.

Lemma bad_vars_eq: forall lvty lsym f,
  bad_vars lvty lsym f = map snd (filter (fun x => negb (f (fst x))) (combine lvty lsym)).
Proof.
  intros lvty lsym f; revert lsym; induction lvty; simpl; intros; auto.
  destruct lsym; auto.
  destruct (f a) eqn : Hfa; simpl; rewrite Hfa; simpl; try f_equal; auto.
Qed.
(*
Definition filter_combine {A B: Type} (l: list A) (l2: list B) (f: A -> bool) : list ( A * B) :=
    filter (fun x => f (fst x)) (combine l l2).
*)
Print typesym.
Lemma vty_inhab_fun_eq: forall ninhab_vars seen_typesyms t n,
vty_inhab_fun ninhab_vars seen_typesyms t n =
((fix check_type (t: vty) : bool :=
match t with
| vty_int => true
| vty_real => true
| vty_var v => negb (in_dec typevar_eq_dec v ninhab_vars)
| vty_cons ts' vtys =>
  (*A super awkward way to get around Coq's termination checker without a nested fixpoint*)
  (*let test : list vty :=
    filter check_type vtys in
  let bvars := map snd (filter (fun x => in_dec vty_eq_dec (fst x) test) 
    (combine vtys (ts_args ts'))) in*)


  (*let bvars := map snd (filter2 vtys (ts_args ts') (fun x => check_type x)) in*)
  (*let bvars : list typevar := nil
    (*bad_vars vtys (ts_args ts') check_type*)
    (*map snd (filter_combine vtys (ts_args ts') check_type)*)
    
    (filter (fun x => check_type (fst x)) (combine vtys (ts_args ts')))*)
    (*bad_vars vtys (ts_args ts') (check_type)*)
    let bvars :=
    ((fix bad_vars (lvty: list vty) (lsym: list typevar) : list typevar :=
    match lvty, lsym with
    | x1 :: t1, x2 :: t2 => if check_type x1 then bad_vars t1 t2 else
      x2 :: bad_vars t1 t2
    | _, _ => nil
    end) vtys (ts_args ts'))
  in
  typesym_inhab_fun bvars seen_typesyms ts' n
end) t).
Proof.
intros. unfold vty_inhab_fun. induction t; try reflexivity.
f_equal. simpl. generalize dependent (ts_args tsym).
induction vs as [| h tl IH]; intros; simpl; try reflexivity.
destruct l eqn : Hargs; try reflexivity.
inversion H; subst. rewrite H2.
destruct l; try reflexivity.
match goal with
| |- context [if ?b then ?c else ?d] => destruct b
end. simpl in IH.
rewrite IH; auto. rewrite IH; auto.
Qed.

Definition constr_inhab_fun (ninhab_vars: list typevar)
(seen_typesyms : list typesym) (c: funsym) (n: nat) :=
forallb (fun t => vty_inhab_fun ninhab_vars seen_typesyms t n) (s_args c).

Lemma constr_inhab_fun_eq: forall ninhab_vars seen_typesyms c n,
constr_inhab_fun ninhab_vars seen_typesyms c n =
((fix forall_ty (lt: list vty) : bool :=
    match lt with
    | nil => true
    | t :: ttl => vty_inhab_fun ninhab_vars seen_typesyms t n && forall_ty ttl
    end) (s_args c)).
Proof.
intros. unfold constr_inhab_fun, forallb. reflexivity.
Qed.

Lemma existsb_ext: forall {A: Type} (f g: A -> bool) (l: list A),
  (forall x, f x = g x) ->
  existsb f l = existsb g l.
Proof.
  intros. induction l; simpl; auto; congruence.
Qed.

Lemma forallb_ext: forall {A: Type} (f g: A -> bool) (l: list A),
  (forall x, f x = g x) ->
  forallb f l = forallb g l.
Proof.
  intros. induction l; simpl; auto; congruence.
Qed.

(*A much more usable definition*)
Lemma typesym_inhab_fun_eq: forall (ninhab_vars: list typevar)
(seen_typesyms : list typesym) (ts: typesym) (n: nat),
typesym_inhab_fun ninhab_vars seen_typesyms ts n =
match n with
| O => false
| S(n') =>
  in_dec typesym_eq_dec ts (sig_t s) && 
  negb (in_dec typesym_eq_dec ts seen_typesyms) &&
  match (find_constrs gamma ts) with
  | None => null ninhab_vars
  | Some constrs => negb (null constrs) && 
    existsb (fun c => constr_inhab_fun ninhab_vars (ts :: seen_typesyms) c n') constrs
  end
end.
Proof.
intros. unfold typesym_inhab_fun.
destruct n; try reflexivity.
destruct (in_dec typesym_eq_dec ts (sig_t s)); try reflexivity.
destruct (in_dec typesym_eq_dec ts seen_typesyms); try reflexivity; simpl.
destruct (find_constrs gamma ts) eqn : Hcon; try reflexivity.
destruct (null l) eqn : Hnull; try reflexivity; simpl.
apply existsb_ext. intros c.
rewrite constr_inhab_fun_eq.
apply forallb_ext. intros v.
rewrite vty_inhab_fun_eq. reflexivity. 
Qed.

(*First, we prove equivalence between the inductive and fixpoint definitions*)

Lemma sublist_greater: forall {A: Type}
(eq_dec: forall (x y : A), {x = y} + {x <> y}) (l1 l2: list A),
sublist l1 l2 ->
length l1 >= length l2 ->
NoDup l1 ->
sublist l2 l1.
Proof.
intros A eq_dec l1. induction l1; simpl; intros.
- assert (length l2 = 0) by lia.
  rewrite length_zero_iff_nil in H2.
  subst. auto.
- inversion H1; subst. unfold sublist.
  intros x Hinx.
  destruct (eq_dec x a); subst. left; reflexivity.
  right. apply (IHl1 (remove eq_dec a l2)); auto.
  + unfold sublist. intros y Hiny.
    destruct (eq_dec y a); subst. contradiction.
    apply in_in_remove; auto. apply H. right. auto.
  + assert (Hlen: In a l2). apply H. left; reflexivity.
    apply (remove_length_lt eq_dec) in Hlen. lia.
  + apply in_in_remove; auto.
Qed.

Lemma existsb_false: forall {A: Type} (f: A -> bool) (l: list A),
  (existsb f l = false) <-> (forall x : A, In x l -> f x = false).
Proof.
  intros; induction l; simpl; split; intros; auto. destruct H0.
  apply orb_false_elim in H. destruct H. destruct H0; subst; auto.
  apply IHl; auto.
  apply orb_false_intro. apply H. left; auto.
  apply IHl; auto.
Qed.

Lemma forallb_false: forall {A: Type} (f: A -> bool) (l: list A),
  (forallb f l = false) <-> (exists x : A, In x l /\ f x = false).
Proof.
  intros. induction l; simpl; split; intros; auto. inversion H. 
  destruct H as [x [[] _]].
  - apply andb_false_iff in H. destruct H.
    + exists a. split; auto.
    + apply IHl in H. destruct H as [x [Hinx Hx]]. exists x; split; auto.
  - apply andb_false_iff. destruct H as [x [[Ha|Hinx] Hx]]; subst.
    left; auto. right; apply IHl. exists x; split; auto.
Qed.

(*TODO: move*)
Lemma combine_NoDup_r: forall {A B: Type} (l1: list A) (l2: list B) (x1 x2 : A) (y: B),
  NoDup l2 ->
  In (x1, y) (combine l1 l2) ->
  In (x2, y) (combine l1 l2) ->
  x1 = x2.
Proof.
  intros A B l1 l2 x1 x2 y. revert l2. induction l1; simpl; intros; auto.
  inversion H0.
  destruct l2; simpl in *. inversion H0.
  inversion H; subst.
  destruct H0; [inversion H0|]; subst.
  destruct H1;[inversion H1|]; subst. reflexivity.
  apply in_combine_r in H1. contradiction.
  destruct H1;[inversion H1|]; subst. 
  apply in_combine_r in H0; contradiction.
  apply (IHl1 l2); auto.
Qed.

(*Proving equivalence is annoying because of the mutual recursion. We prove
  2 intermediate lemmas that rely on the IH of the 3rd, main lemma. Then,
  we use this 3rd lemma to give general versions of the first two:*)
Lemma vty_inhab_iff_aux: forall (recs: list typesym) (badvars: list typevar) (v: vty) (n: nat),
  (forall (badvars : list typevar) (ts : typesym),
  typesym_inhab recs badvars ts (typesym_inhab_fun badvars recs ts n)) ->
  sublist recs (sig_t s) ->
  NoDup recs ->
  n >= length (sig_t s) - length recs ->
  vty_inhab recs badvars v (vty_inhab_fun badvars recs v n).
Proof.
  intros recs b2 v n IH Hsub Hnodup Hn.
  induction v; simpl; try solve[constructor].
  + destruct (in_dec typevar_eq_dec v b2); simpl; constructor; auto.
  + match goal with | |- vty_inhab ?ts ?bs ?v (typesym_inhab_fun ?bb ?x ?y ?n) =>
    remember bb as bvars eqn : Hbad end.
    assert (bvars = bad_vars vs (ts_args tsym) (fun x => vty_inhab_fun b2 recs x n)). {
      subst. clear. generalize dependent (ts_args tsym). clear.
      induction vs; simpl; intros; auto.
      destruct l; auto.
      destruct l; auto.
      destruct (vty_inhab_fun b2 recs a n); try f_equal; auto.
    }
    clear Hbad.
    rewrite bad_vars_eq in H0.
    (*Both cases similar*)
    assert (Hcomb1: forall (x : vty) (y : typevar),
      In (x, y) (combine vs (ts_args tsym)) ->
      ~ In y bvars -> vty_inhab recs b2 x true). {
        subst. intros x y Hinxy C. rewrite in_map_iff in C. 
        destruct (vty_inhab_fun b2 recs x n) eqn : Hinhab.
        - rewrite <- Hinhab. rewrite Forall_forall in H.
          apply H. apply in_combine_l in Hinxy. auto.
        - exfalso. apply C. exists (x, y).
          split; simpl; auto. apply filter_In.
          split; auto. simpl. rewrite Hinhab; auto.
      }
    assert (Hcomb2: forall (x : vty) (y : typevar),
      In (x, y) (combine vs (ts_args tsym)) ->
      In y bvars -> vty_inhab recs b2 x false). { subst.
        intros x y Hinxy. rewrite in_map_iff. intros [[x' y'] [Hy Hin]].
        simpl in Hy; subst. rewrite filter_In in Hin. simpl in Hin; destruct Hin.
        assert (x = x'). {
          eapply combine_NoDup_r. 2: apply Hinxy. all: auto. destruct tsym; simpl.
          apply (reflect_iff _ _ (nodup_NoDup typevar_eq_dec ts_args)). auto.
        }
        subst. rewrite negb_true_iff in H1. rewrite <- H1.
        rewrite Forall_forall in H. apply H. apply in_combine_l in Hinxy. auto.
    }
    destruct (typesym_inhab_fun bvars recs tsym n) eqn : Hts;
      [apply vty_check_consT with (new_tvs:=bvars) | 
        apply vty_check_consF with (new_tvs:=bvars)  ]; auto; rewrite <- Hts;
      apply IH.
Qed.

Lemma constr_inhab_iff_aux: forall (recs: list typesym) (badvars: list typevar)
  (c: funsym) (n: nat),
  (forall (badvars : list typevar) (ts : typesym),
  typesym_inhab recs badvars ts (typesym_inhab_fun badvars recs ts n)) ->
  sublist recs (sig_t s) ->
  NoDup recs ->
  n >= length (sig_t s) - length recs ->
  constr_inhab recs badvars c
    (constr_inhab_fun badvars recs c n).
Proof.
  intros recs b1 c n IH Hsub Hnodup Hn.
  unfold constr_inhab_fun.
  destruct (forallb (fun t : vty => vty_inhab_fun b1 recs t n) (s_args c)) eqn : Hvall.
  - rewrite forallb_forall in Hvall.
    constructor. intros v Hv. rewrite <- (Hvall _ Hv). apply vty_inhab_iff_aux; auto.
  - apply forallb_false in Hvall.
    destruct Hvall as [v [Hinv Hv]].
    apply constr_checkF. exists v; split; auto. rewrite <- Hv.
    apply vty_inhab_iff_aux; auto.
Qed. 

Lemma typesym_inhab_iff: forall (recs: list typesym) (badvars: list typevar)
  (ts: typesym) (n:nat),
  wf_context s gamma ->
  sublist recs (sig_t s) ->
  NoDup recs ->
  n >= length (sig_t s) - length recs ->
  typesym_inhab recs badvars ts (typesym_inhab_fun badvars recs ts n).
Proof.
  intros recs badvars ts n Hwf. revert recs badvars ts.
  induction n; intros;[simpl|]. 
  - assert (sublist (sig_t s) recs) by 
    (apply (sublist_greater typesym_eq_dec _ _ H); auto; lia).
    destruct (in_dec typesym_eq_dec ts (sig_t s)); [|apply ts_check_empty; auto].
    apply ts_check_rec; auto.
  - rewrite typesym_inhab_fun_eq.
    destruct (in_dec typesym_eq_dec ts (sig_t s)); [simpl| apply ts_check_empty; auto].
    destruct (in_dec typesym_eq_dec ts recs); [apply ts_check_rec; auto|simpl].
    destruct (find_constrs gamma ts) eqn : Hcon.
    2 : {
      apply find_constrs_none in Hcon. destruct (null badvars) eqn : Hnull.
      - apply ts_check_typeT; auto.
      - apply ts_check_typeF; auto. rewrite Hnull; auto.
    }
    apply find_constrs_some in Hcon; [| apply Hwf].
    rename l into constrs.
    destruct (null constrs) eqn : Hnull; simpl.
      apply ts_check_adtF1 with(constrs:=constrs); auto.
    (*Now, we need a nested lemma for the constructors - TODO: separate?*)
    assert (Hconstrs: forall badvars (c: funsym),
      constr_inhab (ts :: recs) badvars c (constr_inhab_fun badvars (ts :: recs) c n)). {
      intros b1 c. assert (NoDup (ts :: recs)) by (constructor; auto).
      assert (sublist (ts :: recs) (sig_t s)) by (unfold sublist; simpl;
        intros x; simpl; intros [Hxts| Hxin]; subst; auto).
      apply constr_inhab_iff_aux; auto; simpl; try lia.
      intros. apply IHn; auto. simpl; lia.
    }
    destruct (existsb (fun c : funsym => constr_inhab_fun badvars (ts :: recs) c n) constrs) eqn : Hexcon.
    + apply existsb_exists in Hexcon. destruct Hexcon as [c [Hinc Hc]].
      apply ts_check_adtT with(constrs:=constrs); auto. rewrite Hnull; auto.
      exists c. split; auto. rewrite <- Hc. apply Hconstrs.
    + rewrite existsb_false in Hexcon.
      apply ts_check_adtF2 with(constrs:=constrs); auto.
      rewrite Hnull; auto. intros c Hc. rewrite <- (Hexcon _ Hc). apply Hconstrs.
Qed.

(*One more result: can't be true and false*)
(*TODO (might need all again)*)

(*Some corollaries of the above*)
Corollary constr_inhab_iff: forall (recs: list typesym) (badvars: list typevar)
(c: funsym) (n: nat),
  wf_context s gamma ->
  sublist recs (sig_t s) ->
  NoDup recs ->
  n >= length (sig_t s) - length recs ->
  constr_inhab recs badvars c (constr_inhab_fun badvars recs c n).
Proof.
  intros. apply constr_inhab_iff_aux; auto.
  intros. apply typesym_inhab_iff; auto.
Qed.

Corollary vty_inhab_iff: forall (recs: list typesym) (badvars: list typevar) (v: vty) (n: nat),
  wf_context s gamma ->
  sublist recs (sig_t s) ->
  NoDup recs ->
  n >= length (sig_t s) - length recs ->
  vty_inhab recs badvars v (vty_inhab_fun badvars recs v n).
Proof.
  intros. apply vty_inhab_iff_aux; auto.
  intros. apply typesym_inhab_iff; auto.
Qed.

(*Decidability*)

Corollary typesym_inhab_dec: forall (recs: list typesym) (badvars: list typevar)
  (ts: typesym) (n: nat),
  wf_context s gamma ->
  sublist recs (sig_t s) ->
  NoDup recs ->
  n >= length (sig_t s) - length recs ->
  {typesym_inhab recs badvars ts true} + {typesym_inhab recs badvars ts false}.
Proof.
  intros. destruct (typesym_inhab_fun badvars recs ts n) eqn : Hfun.
  left. rewrite <- Hfun. apply typesym_inhab_iff; auto.
  right. rewrite <- Hfun. apply typesym_inhab_iff; auto.
Defined.

(*TODO: show both cannot be true*)

(*Now, we want to show that this actually corresponds to inhabited types*)


 
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

