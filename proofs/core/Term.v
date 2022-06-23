Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.
(*From Dblib Require Import DblibTactics DeBruijn Environments.*)
(* A smaller core language of types and terms *)
Import ListNotations.

Require Import Util.

(** Types **)

(*Type variable (ex: a)*)
Definition typevar : Type := string. 

Definition typevar_eq_dec : forall (t1 t2: typevar),
  {t1 = t2} + {t1 <> t2} := string_dec.

(*Type symbol (ex: list a)*)
Record typesym : Type := mk_ts {
  ts_name : string;
  ts_arity: nat
  }.

Lemma typesym_eq_dec: forall (t1 t2: typesym),
  {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality. apply Nat.eq_dec. apply string_dec.
Defined.

(*Value types*)
Inductive vty : Type :=
  | vty_int : vty
  | vty_real : vty
  (*| vty_bool : vty
  | vty_func: vty -> vty -> vty
  | vty_pred: vty -> vty*)
  (*| vty_tuple: vty -> vty -> vty*)
  | vty_var: typevar -> vty
  | vty_cons: typesym -> list vty -> vty. (*TODO: do we need this? Can we make it non-list?*)

Definition vty_eq_dec: forall (v1 v2: vty), {v1 = v2} + {v1 <> v2}.
Admitted.
(*TODO: need better induction*)

(*Type substitution (assign meaning to a type variables)*)
Fixpoint ty_subst_single (v: typevar) (t: vty) (expr: vty) : vty :=
  match expr with
  | vty_int => vty_int
  | vty_real => vty_real
  | vty_var tv => if typevar_eq_dec v tv then t else vty_var tv
  | vty_cons ts typs =>
      vty_cons ts (map (ty_subst_single v t) typs)
  end.

(*Substitute a list of typevars*)
Definition ty_subst (vs: list typevar) (ts: list vty) (expr: vty) : vty :=
  fold_right (fun x acc => ty_subst_single (fst x) (snd x) acc) expr (combine vs ts).

Definition ty_subst_list (vs: list typevar) (ts: list vty) (exprs: list vty) : list vty :=
  map (ty_subst vs ts) exprs.

(* Sorts *)

(*Get the type variables in a type. There may be duplicates, but that is fine*)
Fixpoint type_vars (t: vty) : list typevar :=
  match t with
  | vty_int => nil
  | vty_real => nil
  | vty_var v => [v]
  | vty_cons sym ts => fold_right (fun x acc => type_vars x ++ acc) nil ts
  end.
  
Definition is_sort (t: vty) : bool :=
  match (type_vars t) with
  | nil => true
  | _ => false
  end.

Definition sort : Type := {t: vty | is_true (is_sort t)}.
(*TODO: see if we need an alternate definition*)

Lemma int_is_sort: is_true (is_sort vty_int).
Proof.
  unfold is_sort; simpl. auto.
Qed.

Definition s_int : sort := exist _ vty_int int_is_sort.

Lemma real_is_sort: is_true (is_sort vty_real).
Proof.
  unfold is_sort; simpl. auto.
Qed.

Definition s_real : sort := exist _ vty_real real_is_sort.

Definition sublist {A: Type} (l1 l2: list A) : Prop :=
    forall x, In x l1 -> In x l2.

(*We want to know that when we substitute in sorts for type variables,
  the result is a sort *)
(*TODO: this - after we have better induction principle for types*)


(** Function and Predicate Symbols **)

Record funsym :=
  {
    s_name : string;
    s_params : list typevar;
    s_args: list vty;
    s_ret: vty;
    (*Well-formed - all type variables appear in params*)
    s_ret_wf: sublist (type_vars s_ret) s_params;
    s_args_wf: forall x, In x s_args -> sublist (type_vars x) s_params
  }.

Record predsym :=
  {
    p_name: string;
    p_params: list typevar;
    p_args : list vty;
    p_args_wf: forall x, In x p_args -> sublist (type_vars x) p_params
  }.

(*As an example, we define the polymorphic identity function*)
Section ID.

Definition id_name : string := "id".
Definition a : string := "a".
Definition id_params : list typevar := [a].
Definition id_args: list vty := [vty_var a].
Definition id_ret: vty := vty_var a.
Lemma id_ret_wf: sublist (type_vars id_ret) id_params.
Proof.
  simpl. unfold id_params, sublist. auto.
Qed.
Lemma id_args_wf: forall x, In x id_args -> sublist (type_vars x) id_params.
Proof.
  intros x. simpl. intros [Hx| []]; subst. simpl. unfold id_params, sublist.
  auto.
Qed. Print funsym.
Definition idsym := Build_funsym id_name id_params id_args id_ret id_ret_wf id_args_wf.

End ID.

(** Syntax - Terms and Formulas **)

Inductive constant : Type :=
  | ConstInt : Z -> constant
  | ConstReal : R -> constant
  | ConstStr : string -> constant.

Inductive quant : Type :=
    | Tforall
    | Texists.

Inductive binop : Type :=
    | Tand
    | Tor
    | Timplies
    | Tiff.

Unset Elimination Schemes.
(*TODO: nats or strings for variables - substitution should not
  be problem bc only substitute values*)
(*No case/match at the moment*)
Inductive term : Type :=
  | Tconst: constant -> term
  | Tvar : nat -> vty -> term
  | Tfun: funsym -> list vty -> list term -> term
  | Tlet: term -> vty -> term -> term
  | Tif: formula -> term -> term -> term
with formula : Type :=
  | Fpred: predsym -> list vty -> list term -> formula
  | Fquant: quant -> vty -> formula -> formula
  | Feq: vty -> term -> term -> formula
  | Fbinop: binop -> formula -> formula -> formula
  | Fnot: formula -> formula
  | Ftrue: formula
  | Ffalse: formula
  | Flet: term -> vty -> formula -> formula
  | Fif: formula -> formula -> formula -> formula.
  (*TODO: will need nicer (useful) induction scheme*)
  Set Elimination Schemes.

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
    length vs = (ts_arity ts) ->
    Forall (fun x => valid_type s x) vs ->
    valid_type s (vty_cons ts vs).
Notation "s '|-' t" := (valid_type s t) (at level 40).

(* Typing rules for terms *)
Inductive term_has_type: sig -> term -> vty -> Prop :=
  | T_int: forall s z,
    term_has_type s (Tconst (ConstInt z)) vty_int
  | T_real: forall s r,
    term_has_type s (Tconst (ConstReal r)) vty_real
  | T_Var: forall s x ty,
    s |- ty ->
    term_has_type s (Tvar x ty) ty
  | T_Fun: forall s (params : list vty) (tms : list term) (f: funsym),
    In f (sig_f s) ->
    Forall (valid_type s) params ->
    length tms = length (s_args f) ->
    length params = length (s_params f) ->
    (* For all i, [nth i tms] has type [sigma(nth i (s_args f))], where
      sigma is the type substitution that maps f's type vars to [params] *)
    Forall (fun x => term_has_type s (fst x) (snd x)) (combine tms
      (map (ty_subst (s_params f) params) (s_args f))) ->
    term_has_type s (Tfun f params tms) (s_ret f)
  | T_Let: forall s t1 ty t2 ty2,
    term_has_type s t1 ty ->
    term_has_type s t2 ty2 ->
    term_has_type s (Tlet t1 ty t2) ty2
    (*TODO: make sure this works with nats as vars*)
  | T_If: forall s f t1 t2 ty,
    valid_formula s f ->
    term_has_type s t1 ty ->
    term_has_type s t2 ty ->
    term_has_type s (Tif f t1 t2) ty

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
  | F_Quant: forall s q ty f,
    valid_type s ty ->
    valid_formula s f ->
    valid_formula s (Fquant q ty f)
  | F_Pred: forall s (params: list vty) (tms: list term) (p: predsym),
    (*Very similar to function case*)
    In p (sig_p s) ->
    Forall (valid_type s) params ->
    length tms = length (p_args p) ->
    length params = length (p_params p) ->
    Forall (fun x => term_has_type s (fst x) (snd x))
      (combine tms (map (ty_subst (p_params p) params) (p_args p))) ->
    valid_formula s (Fpred p params tms)
  | F_Let: forall s t ty f,
    term_has_type s t ty ->
    valid_formula s f ->
    valid_formula s (Flet t ty f)
  | F_If: forall s f1 f2 f3,
    valid_formula s f1 ->
    valid_formula s f2 ->
    valid_formula s f3 ->
    valid_formula s (Fif f1 f2 f3)
  | F_Eq: forall s ty t1 t2,
    term_has_type s t1 ty ->
    term_has_type s t2 ty ->
    valid_formula s (Feq ty t1 t2).

Notation "s '|-' t ':' ty" := (term_has_type s t ty) (at level 40).
Notation "s '|-' f" := (valid_formula s f) (at level 40).

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
      Nat.eqb (length vs) (ts_arity ts) &&
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
Admitted.
(*need better induction principle*)
(*
Fixpoint typecheck_term (t: term) : option vty :=
  match t with
  | Tconst (ConstInt _) => Some vty_int
  | Tconst (ConstReal _) => Some vty_real
  | Tconst _ => None (*for now*)
  | Tvar n v => if typecheck_type v then Some v else None
  (*TODO: later*)
*)
(** Semantics **)

(*Need to prove that this gives sort*)

Fixpoint curry (l: list Type) (ret: Type) : Type :=
  match l with
  | nil => ret
  | x :: t => x -> (curry t ret)
  end.

  (*Using sorts gives lots of dependent proof obligations anywhere, so we give
    a slightly different version where we give every type a Type rather than
    just sorts. We will later prove that we are only dealing with sorts
    TODO: is this the way to do it? Not sure *)

Record pre_interp := {
  domain: vty -> Type;
  domain_int: domain vty_int = Z;
  domain_real: domain vty_real = R;

  (*This is quite unwieldy (and could be wrong) - need to see if works/can do better*)

  funs: forall (f:funsym) (s: list vty),
    curry (map domain (ty_subst_list (s_params f) s (s_args f)))
      (domain (ty_subst (s_params f) s (s_ret f)));
  preds: forall (p:predsym) (s: list vty),
    curry (map domain (ty_subst_list (p_params p) s (p_args p)))
      Prop
}.

(*Substitute according to function - TODO*)
Fixpoint v_subst (v: typevar -> vty) (t: vty) : vty :=
  match t with
  | vty_int => vty_int
  | vty_real => vty_real
  | vty_var tv => v tv
  | vty_cons ts vs => vty_cons ts (map (v_subst v) vs)
  end.

(*Valuations*)
Record valuation (i: pre_interp) := {
  v_typevar : typevar -> vty;
  v_vars: forall (n: nat) (v: vty), (domain i (v_subst (v_typevar) v))
}.

Section Interp.

Variable i: pre_interp.

Definition val (v: valuation i) t : Type := domain i (v_subst (v_typevar i v) t).

(*TODO: is this the right approach?*)
Definition z_to_dom (v: valuation i) (z: Z) : val v vty_int.
Proof.
  unfold val. simpl. rewrite (domain_int i). apply z.
Defined.

Definition r_to_dom (v: valuation i) (r: R) : val v vty_real.
Proof.
  unfold val. simpl. rewrite (domain_real i). apply r.
Defined.

Definition var_to_dom (v: valuation i) (n: nat) (t: vty) : val v t.
Proof.
  unfold val. apply v_vars. apply n.
Defined. 

(*Substitution*)

(*Here, a substitution means that we replace a variable of type t
  with an element of [val t]. This affects the valuation v:
  ie: v' := v[x -> y], where y \in [[v(t)]]
  We will prove that, for all tm, [[tm]]_v' = [[tm]]_v.
  We will always be replacing variable 0 in a term (the innermost bound variable)
  *)

Definition substi (v: valuation i) (ty: vty) (y: val v ty) : valuation i.
apply (Build_valuation i (v_typevar i v)).
intros m ty'. destruct (m =? 0).
destruct (vty_eq_dec ty ty').
- subst. apply y.
- (*trivial case*) apply (v_vars i v m ty').
- apply (v_vars i v (m - 1) ty').
Defined.

Definition bool_of_binop (b: binop) : bool -> bool -> bool :=
  match b with
  | Tand => andb
  | Tor => orb
  | Timplies => implb
  | Tiff => eqb
  end.

(* Semantics/Interpretation *)
(*Difficulty - should only be defined for well-typed terms - will we need
  dependent types?*)

(*TODO: is the underlying logic supposed to be classical or constructive?
  Seemingly classical in paper because formula interpretations are equal to bool.
  We can assume LEM and write a function to evaluate a term/formula instead, 
  should we do this?*)

Inductive term_interp: 
  forall (v: valuation i) (tm: term) (ty: vty) (x: domain i (v_subst (v_typevar i v) ty)), Prop :=
  | TI_int: forall v z,
    term_interp v (Tconst (ConstInt z)) vty_int (z_to_dom v z)
  | TI_real: forall v r,
    term_interp v (Tconst (ConstReal r)) vty_real (r_to_dom v r)
  | TI_var: forall v (n: nat) (ty: vty),
    term_interp v (Tvar n ty) ty (var_to_dom v n ty)
  | TI_iftrue: forall v f t1 t2 ty x,
    formula_interp v f true ->
    term_interp v t1 ty x ->
    term_interp v (Tif f t1 t2) ty x
  | TI_iffalse: forall v f t1 t2 ty x,
    formula_interp v f false ->
    term_interp v t2 ty x ->
    term_interp v (Tif f t1 t2) ty x
  (*substitution changes the valuation *)
  | TI_let: forall v t1 t2 ty1 ty2 x1 x2,
    term_interp v t1 ty1 x1 ->
    term_interp (substi v ty1 x1) t2 ty2 x2 ->
    term_interp v (Tlet t1 ty1 t2) ty2 x2
  | TI_func: forall v (f: funsym) (params: list vty) (ts: list term) ty xs x,
    let tys := ty_subst_list (s_params f) params  
    Forall (fun x => term_interp v (fst x) (snd x)) (combine (combine (s_args ) ts xs) ->
    term_interp v 
  (*Only 1 left: function TODO: I think we need sorts for this*)

with formula_interp: (valuation i) -> formula -> bool -> Prop :=
  | FI_true: forall v, formula_interp v Ftrue true
  | FI_false: forall v, formula_interp v Ffalse false
  | FI_not: forall v f b,
    formula_interp v f b ->
    formula_interp v (Fnot f) (negb b)
  | FI_binop: forall v b f1 f2 b1 b2,
    formula_interp v f1 b1 ->
    formula_interp v f2 b2 ->
    formula_interp v (Fbinop b f1 f2) (bool_of_binop b b1 b2)
  | FI_iftrue: forall v f f1 f2 b,
    formula_interp v f true ->
    formula_interp v f1 b ->
    formula_interp v (Fif f f1 f2) b
  | FI_iffalse: forall v f f1 f2 b,
    formula_interp v f false ->
    formula_interp v f2 b ->
    formula_interp v (Fif f f1 f2) b
  | FI_let: forall v t ty f x b,
    term_interp v t ty x ->
    formula_interp (substi v ty x) f b ->
    formula_interp v (Flet t ty f) b
  | FI_forallT: forall v ty f,
    (forall x, formula_interp (substi v ty x) f true) ->
    formula_interp v (Fquant Tforall ty f) true
  | FI_forallF: forall v ty f, (*otherwise we cannot prove that forall is false*)
    (exists x, formula_interp (substi v ty x) f false) ->
    formula_interp v (Fquant Tforall ty f) false
  | FI_existsT: forall v ty f,
    (exists x, formula_interp (substi v ty x) f true) ->
    formula_interp v (Fquant Texists ty f) true
  | FI_existsF: forall v ty f,
    (forall x, formula_interp (substi v ty x) f false) ->
    formula_interp v (Fquant Texists ty f) false
  | FI_eqT: forall v ty t1 t2 x1 x2, (*TODO: assume decidable equality?*)
    term_interp v t1 ty x1 ->
    term_interp v t2 ty x2 ->
    x1 = x2 ->
    formula_interp v (Feq ty t1 t2) true
  | FI_eqF: forall v ty t1 t2 x1 x2,
    term_interp v t1 ty x1 ->
    term_interp v t2 ty x2 ->
    x1 <> x2 ->
    formula_interp v (Feq ty t1 t2) false
    .
(*TODO: functions and predicates*)

Lemma test1: forall {A: Type} (P: A -> Prop),
  (forall x, ~(P x)) ->
  ~ (exists x, P x).
Proof.
  intros A P Hall [x Hex]. assert (~ (P x)) by apply Hall. auto.
Qed.

Lemma test2: forall {A: Type} (P: A -> Prop),
  (exists x, ~(P x)) ->
  ~(forall x, P x).
Proof.
  intros A P [x Hx] Hall. assert (P x) by apply Hall. auto.
Qed.

(*Let's give an example: prove that equality is reflexive*)
Lemma prove_eq_refl: forall (v: valuation i) (a: vty),
  formula_interp v (Fquant Tforall a (Feq a (Tvar 0 a) (Tvar 0 a))) true.
Proof.
  intros v a. constructor. intros x.
  eapply FI_eqT. 
  - apply TI_var.
  - apply TI_var.
  - reflexivity. 
Qed.
