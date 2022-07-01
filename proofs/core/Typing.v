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

(*Fixpoint vty_inhab (f: typesym -> list funsym) 
  (ninhab_vars: list typevar) (seen_typesyms: list typesym) (t: vty) : bool :=
  match t with
  | vty_int => true
  | vty_real => true
  | vty_var v => negb (in_dec typevar_eq_dec v ninhab_vars)
  | vty_cons ts vtys => 
    let bad_vars : list typevar := nil (*TODO*) in
    typesym_inhab f bad_vars seen_typesyms ts
  end.*)

(*If we want this to be efficient, put in a map*)
Definition get_constrs (gamma: context) (ts: typesym) : list funsym :=
  fold_right (fun x acc => if typesym_eq_dec ts (fst x) then (snd x) else acc) nil
    (datatypes_of_context gamma).


(*Instead, we want an inductive definition of what it means for a 
  type/typesym/constructor to be inhabited*)
  (*Note: we assume that a type variable has been applied to an inhabited type*)
(*No, we need more: ex: type 'a foo, type list = foo list*)
(*And this doesnt work for recursive types: it allows us to prove when
  something is inhabited, but we can't prove something isnt inhabited*)
  (*
Unset Elimination Schemes.
Inductive vty_inhab (s: sig) (gamma: context) : list typevar -> vty -> Prop :=
  | Int_inhab: forall l, vty_inhab s gamma l vty_int
  | Real_inhab: forall l, vty_inhab s gamma l vty_real
  | Var_inhab: forall v l,
    ~ In v l ->
    vty_inhab s gamma l (vty_var v)
  | Cons_inhab: forall ts vs l,
    (forall v, In v l <-> exists t, In (t, v) (combine vs (ts_args ts)) /\ )
    Forall (vty_inhab s gamma l) vs ->
    typesym_inhab s gamma ts l ->
    vty_inhab s gamma l (vty_cons ts vs)

with typesym_inhab (s: sig) (gamma: context) : list typevar -> typesym -> Prop :=
  | Sym_inhab: forall ts l,
    get_constrs gamma ts = nil ->
    typesym_inhab s gamma ts l
  | ADT_inhab: forall ts f fs,
    get_constrs gamma ts = f :: fs ->
    (exists c, In c (f :: fs) /\ Forall (fun t => vty_inhab s gamma t) (s_args f)) ->
    typesym_inhab s gamma ts.
Set Elimination Schemes.

Scheme vty_inhab_ind := Minimality for vty_inhab Sort Prop
with typesym_inhab_ind := Minimality for typesym_inhab Sort Prop.

Require Import Coq.Program.Equality.

Lemma vty_inhab_correct: forall s gamma ty,
  wf_context s gamma ->
  (forall ts, In ts (sig_t s) -> get_constrs gamma ts = nil ->
    exists tm vs, closed_term tm /\ term_has_type s tm (vty_cons ts vs)) ->
  (vty_inhab s gamma ty) -> (exists tm, closed_term tm /\ term_has_type s tm ty).
Proof.
  Check vty_inhab_ind.
  intros s gamma ty Hcon Hconstrs. revert ty.
  apply (vty_inhab_ind s gamma (fun ty => exists tm, closed_term tm /\ term_has_type s tm ty)
    (fun ts => exists tm vty, closed_term tm /\ term_has_type s tm (vty_cons ts vty))).
  - exists (Tconst (ConstInt 0%Z)). split; auto. constructor.
  - exists (Tconst (ConstReal R0)). split; auto. constructor.
  -  
  intros. split; intros.
  - admit.
  - destruct H1 as [tm [Hclose Hty]]. induction ty; try solve[constructor].
    constructor. rewrite Forall_forall in H1.
    rewrite Forall_forall. intros. apply H1; auto. 
    inversion Hty; subst; auto. inversion Hclose.
    Print term
    
    constructor. try constructor. 


    inversion Hty; subst. inversion Hclose.
    constructor. inver
  dependent induction Hty; try solve[constructor].
    + inversion Hclose.
    + 
    
    
    simpl in Hclose. 
    
    
    constructor.
    + contructor. 
  induction H1.

(*We show that this *)

(*Show that this i*)
*)

(*NOTE: not correct at the moment - need to know that typesym exists there*)

(*With no polymorphism, easy: look through constructors, look at types.
  For each type, either base type OR we look up, see if exists in context
  If not, return false
  If it exists but is equal to current type, return false (for constructor)
  Otherwise, if that type exists (not depending on current symbol), then good
  
  In that case, seeing if a type exists does the following:
  take in l, list of not-allowed type symbols
  if int or real, return true
  else, if user-define - look up in context,
  if does not exist or if is l, return false
  otherwise, if it has no constructors, return true
  otherwise, recursively see if this exists

  So: this would actually prove: if returns true, we can construct an instance of this type

  problem: now we have type variables and polymorphism
  so we still look through constructors at type list
  but now - a given type variable for a constructor may be applied to a badly-formed type
  HOWEVER, even if this is the case, it is not necessarily the case that this type variable
  is ever used
  (I think this can come up in mutual recursion - we cant assume all referenced types come
  previously, in which case they exist)

  for example, say we have the following:
  type foo 'a 'b = FOO 'a
  type bar = B1 (FOO int baz)
  with baz = B2 baz.
  B2 is not well-founded BUT B1 is

  alternately - I believe that the only case where this can come up is with
  mutually recursive types, other types have been previously checked
  BUT, not really a problem, since the checking of that type will fail

  except if we have
  type foo = F bar
  with bar = C foo

  SO, we cannot assume the existence of other types, but we can say the following:
  check all types assuming that all of these are false
  if any pass, remove that from the list of false ones and list to check and check again
  continue until none pass or all are gone
  I think this should work but it is inefficient

  Basically the problem is: what can we say about the types we are checking?
  Assume that all type variables not in the list are inhabited by a closed term
  If a type passes the check, then it is inhabited by a closed term (modulo l)
  And for type symbols, if it passes the check, then for any type arguments
  of the correct length and which are inhabited by a closed term, vty_cons ts vs
  is inhabited by a closed term

  Key case: if t = vty_cons ts' vs' and we know that vty_inhab t holds,
    then we have that typesym_inhab (bad_vars) ... ts' = true
    so how do we know that this type is inhabited
    by IH, would need to know that vs' are all inhabited

    that's the problem: we DON'T check the types when we check a typesym in vty_check
    ONLY to make sure that we dont use any bad type symbols
    so if we have List bad, we check List under the assumption that we don't use 'a in any
    constructors
    we are NOT saying that List bad is inhabited (but it is, because we dont use any 'a)

    TODO: FIGURE THIS OUT
  
  it is inhabited by a closed term
  If a type passes the check, then 

  alternate method (let's see):
  take in a list of known types (or typesymbols)
  also take in a list of possibly-mutual-recursive types (ie: can't assume any exist)
  then evaluate a declaration (of a particular type) as follows:
  look at a given constructor, if all are previously-known types 
  then evaluate a declaration

  *)

(*Give fuel for termination*)
(*This is a terrible definition because we need to convince Coq that it terminates.
  So we need lots of manual "fix" rather than existsb, forallb, fold_right, etc*)
Fixpoint typesym_inhab (f: typesym -> list funsym) (ninhab_vars: list typevar)
  (seen_typesyms : list typesym) (ts: typesym) (n: nat) : bool :=
  match n with
  | O => false
  | S(n') =>
    if in_dec typesym_eq_dec ts seen_typesyms then false else
    match (f ts) with
    | nil => null ninhab_vars
    | _ :: _ =>
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
                    | nil, nil => nil
                    | x1 :: t1, x2 :: t2 => if check_type x1 then bad_vars t1 t2 else
                      x2 :: bad_vars t1 t2
                    | _, _ => nil
                    end) vtys (ts_args ts'))
                  in
                  typesym_inhab f bvars (ts :: seen_typesyms) ts' n'
                end) t) && forall_ty ttl
            end) (s_args c)) || (exists_constr tl)
        end) (f ts)
      end
    end.

(*We didn't want to write it with mutual recursion, but we can simplify now:*)
Fixpoint vty_inhab (f: typesym -> list funsym) (ninhab_vars: list typevar)
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
      | x1 :: t1, x2 :: t2 => if vty_inhab f ninhab_vars seen_typesyms x1 n 
        then bad_vars t1 t2 else x2 :: bad_vars t1 t2
      | _, _ => nil
      end) vtys (ts_args ts')) in
    typesym_inhab f bvars (seen_typesyms) ts' n
  end.

(*Definition forallb_eq: forall {A: Type} (P: A -> bool) (l: list A),
  (fix name (l': list A) : bool :=
    match l' with
    | nil => true
    | h :: t => P h && name t
    end) l = forallb P l.
Proof.
  intros. unfold forallb. reflexivity.
Qed.*)
Lemma vty_inhab_eq: forall f ninhab_vars seen_typesyms t n,
  vty_inhab f ninhab_vars seen_typesyms t n =
  ((fix check_type (t: vty) : bool :=
  match t with
  | vty_int => true
  | vty_real => true
  | vty_var v => negb (in_dec typevar_eq_dec v ninhab_vars)
  | vty_cons ts' vtys =>
    let bvars : list typevar :=
      ((fix bad_vars (lvty: list vty) (lsym: list typevar) : list typevar :=
      match lvty, lsym with
      | nil, nil => nil
      | x1 :: t1, x2 :: t2 => if check_type x1 then bad_vars t1 t2 else
        x2 :: bad_vars t1 t2
      | _, _ => nil
      end) vtys (ts_args ts'))
    in
    typesym_inhab f bvars seen_typesyms ts' n
  end) t).
Proof.
  intros. unfold vty_inhab. induction t; try reflexivity.
  f_equal. simpl. generalize dependent (ts_args tsym).
  induction vs as [| h tl IH]; intros; simpl; try reflexivity.
  destruct l eqn : Hargs; try reflexivity.
  inversion H; subst. rewrite H2.
  match goal with
  | |- context [if ?b then ?c else ?d] => destruct b
  end. simpl in IH.
  rewrite IH; auto. rewrite IH; auto.
Qed. 

Definition constr_inhab (f: typesym -> list funsym) (ninhab_vars: list typevar)
(seen_typesyms : list typesym) (c: funsym) (n: nat) :=
  forallb (fun t => vty_inhab f ninhab_vars seen_typesyms t n) (s_args c).

Lemma constr_inhab_eq: forall f ninhab_vars seen_typesyms c n,
  constr_inhab f ninhab_vars seen_typesyms c n =
  ((fix forall_ty (lt: list vty) : bool :=
      match lt with
      | nil => true
      | t :: ttl => vty_inhab f ninhab_vars seen_typesyms t n && forall_ty ttl
      end) (s_args c)).
Proof.
  intros. unfold constr_inhab, forallb. reflexivity.
Qed.


Lemma typesym_inhab_eq: forall (f: typesym -> list funsym) (ninhab_vars: list typevar)
(seen_typesyms : list typesym) (ts: typesym) (n: nat),
  typesym_inhab f ninhab_vars seen_typesyms ts n =
  match n with
  | O => false
  | S(n') => if in_dec typesym_eq_dec ts seen_typesyms then false else
    match (f ts) with
    | nil => null ninhab_vars
    | _ :: _ => existsb (fun c => constr_inhab f ninhab_vars (ts :: seen_typesyms) c n') (f ts)
    end
  end.
Proof.
  intros. unfold typesym_inhab.
  destruct n; try reflexivity.
  destruct (in_dec typesym_eq_dec ts seen_typesyms); try reflexivity.
  destruct (f ts) eqn : Hcons; [reflexivity|].
  simpl. f_equal.
  - rewrite constr_inhab_eq. simpl.
Admitted.


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

(*NOTE: NOT true that typesym inhab -> arguments are inhabited
  ex: type 'a foo = F1 | F2, type bad = B bad, then
  type ok = A (bad foo)
  OK can be built even though bad does not exist
  so what does vty_inhab even mean?
  *)

(*We need LOTS of hypotheses for induction, most of these will become trivial
  in the final lemma because ninhab_vars and seen_typesyms will be nil *)
Lemma typesym_inhab_correct: forall (s: sig) (gamma: context)
  (ninhab_vars : list typevar) (seen_typesyms: list typesym) (ts: typesym) (n: nat),
  wf_context s gamma ->
  In ts (sig_t s) ->
  sublist seen_typesyms (sig_t s) ->
  NoDup seen_typesyms ->
  Forall (fun t => ~ exists tm vs, term_has_type s tm (vty_cons t vs)) seen_typesyms ->
  Forall (fun v => In v (ts_args ts) /\ ~exists tm, term_has_type s tm (vty_var v)) ninhab_vars ->
  (forall ts, null ninhab_vars -> get_constrs gamma ts = nil -> forall vs,
    Forall (fun t => exists tm, term_has_type s tm t) vs -> exists tm , 
    term_has_type s tm (vty_cons ts vs)) ->
  n >= length (sig_t s) - length seen_typesyms ->
  typesym_inhab (get_constrs gamma) ninhab_vars seen_typesyms ts n = true ->
  forall (vs: list vty), Forall (fun t => exists tm, term_has_type s tm t) vs ->
  exists tm, term_has_type s tm (vty_cons ts vs).
Proof.
  intros. generalize dependent ts. generalize dependent ninhab_vars.
  generalize dependent seen_typesyms. generalize dependent vs. 
  induction n; intros vs Hvs seen Hsub Hnodup Hallseen Hn
  ninhab Hninhab ts Hints Hallninhab; rewrite typesym_inhab_eq; intros Hty;[inversion Hty|].
  destruct (in_dec typesym_eq_dec ts seen); [inversion Hty|].
  destruct (get_constrs gamma ts) eqn : Hcon.
    apply Hninhab; auto.
  rewrite existsb_exists in Hty.
  destruct Hty as [constr [Hinconstr Hconstr]].
  (*Here, we need a lemma for constr_inhab*)
  unfold constr_inhab in Hconstr.
  rewrite forallb_forall in Hconstr.
  (*Here, we need a lemma for vty_inhab*)
  assert (forall ty ninhab' seen', vty_inhab (get_constrs gamma) ninhab' seen' ty n = true ->
    exists (tm: term), term_has_type s tm ty). {
      intros ty. induction ty; simpl; auto.
      - admit.
      - admit.
      - admit.
      - intros.  apply IHn in H1; auto.
        rewrite Forall_forall.  rewrite Forall_forall in H0.
        intros. eapply H0. assumption. 
    }
  
  destruct ninhab_vars as [| v1 vtl]; simpl in H7; try solve[inversion H7].
  
  
  
  
  split; intros; auto. inversion H7.
    rewrite Forall_forall in H3. exfalso.
    apply (H3 ts); auto.
    assert (sublist (sig_t s) seen_typesyms). {
      apply sublist_greater; auto. apply typesym_eq_dec. lia.
    }
    apply H8. auto.
  - destruct (in_dec typesym_eq_dec ts seen_typesyms); auto.
    + split; intros C; try solve[inversion C].
      exfalso. rewrite Forall_forall in H3. apply (H3 ts); auto.
    + destruct (get_constrs gamma ts) eqn : Hcon; simpl.
      * split; intros; [apply H5; auto |].
        destruct H7 as [tm [vs Hty]]. inversion Hty; subst.
        inversion H7; subst.
        inversion Hty; subst.
        {
          apply H5; auto. 
        } 

    unfold sublist in H7. apply H7.
    apply sublist_greater.

    



  

  
  
  generalize dependent s. revert gamma ninhab_vars seen_typesyms ts. generalize dependent ts. generalize dependent seen_typesyms.  induction n


  In ts (typesyms_of_def) ->
  Forall (fun x => In x l) seen_typesyms ->
  n >= length l ->
  typesym_inhab ts = true <-> 

(*Instead of mutual recursion, we give names to the different sub-functions*)
Definition vty_inhab (f: typesym -> list funsym) 
  (ninhab_vars: list typevar) (seen_typesyms: list typesym) (t: vty) (n: nat) : bool :=
  match t with
  | vty_int => true
  | vty_real => true
  | vty_var v => negb (in_dec typevar_eq_dec v ninhab_vars)
  | vty_cons ts' vtys =>
    let bad_vars : list typevar := nil (*TODO*) in
    typesym_inhab f bad_vars (seen_typesyms) ts' n
  end.

Definition constructor_inhab (f: typesym -> list funsym) (ninhab_vars: list typevar)
(seen_typesyms : list typesym) (c: funsym) (n: nat) : bool :=
forallb (fun t => vty_inhab f ninhab_vars seen_typesyms t n) (s_args c).

Lemma typesym_inhab_eq: forall 

  existsb 
    (fun c => forallb (fun t =>
    match t with
    | vty_int => true
    | vty_real => true
    | vty_var v => negb (in_dec typevar_eq_dec v ninhab_vars)
    | vty_cons ts vtys => 
      let bad_vars : list typevar := nil (*TODO*) in
      typesym_inhab f bad_vars (ts :: seen_typesyms) ts
    end)(s_args c)) (f ts)
  end.

with constructor_inhab (f: typesym -> list funsym) (ninhab_vars: list typevar)
  (seen_typesyms : list typesym) (c: funsym) : bool :=
  forallb (fun t => vty_inhab f ninhab_vars seen_typesyms t) (s_args c).


Fixpoint vty_inhab (f: typesym -> list funsym) 
  (ninhab_vars: list typevar) (seen_typesyms: list typesym) (t: vty) : bool :=
  match t with
  | vty_int => true
  | vty_real => true
  | vty_var v => negb (in_dec typevar_eq_dec v ninhab_vars)
  | vty_cons ts vtys => 
    let bad_vars : list typevar := nil (*TODO*) in
    typesym_inhab f bad_vars seen_typesyms ts
  end
with typesym_inhab (f: typesym -> list funsym) (ninhab_vars: list typevar)
  (seen_typesyms : list typesym) (ts: typesym) : bool :=
  match (f ts) with
  | nil => true (*TODO*)
  | _ :: _ => existsb 
    (fun c => constructor_inhab f ninhab_vars (ts :: seen_typesyms) c) (f ts)
  end

with constructor_inhab (f: typesym -> list funsym) (ninhab_vars: list typevar)
  (seen_typesyms : list typesym) (c: funsym) : bool :=
  forallb (fun t => vty_inhab f ninhab_vars seen_typesyms t) (s_args c).
  
(*Will prove by showing that this implies existence of a type*)