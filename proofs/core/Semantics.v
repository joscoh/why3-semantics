Require Import Types.
Require Import Syntax.
Require Import Typing.
Require Import IndTypes.
Require Import Hlist.

Require Import Coq.Program.Equality.
Require Import Coq.Logic.Eqdep_dec.

(** Semantics **)



(*Definition predsym_sigma_args (p: predsym) (s: list sort) : list sort :=
  ty_subst_list_s (p_params p) s (p_args p).*)

Inductive domain_nonempty (domain: sort -> Type) (s: sort) :=
  | DE: forall (x: domain s),
    domain_nonempty domain s.

Definition dom_cast_aux (domain: sort -> Type) (v1 v2: sort) (Hv: v1 = v2) 
  (x: domain v1) : domain v2.
subst. apply x.
Defined.

Section Interp.

Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma).

(*A pre-interpretation includes a map from sorts to Set, the condition that
  all of these Sets are nonempty, interpretations for functions and predicates,
  the requirement that all ADT domains are [adt_rep], and the
  requirement that all constructor domains are [constr_rep]
  (we will later add restrictions on functions and predicates).
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

(*TODO: separate into v_typevar and v_vars
  in denotational: fix v_typevar, let v_vars be general
  then the output ONLY depends on v_typevar so no
  dependent type issues*)
(*Valuations*)
Definition val_typevar := typevar -> sort.
(*
Record val_typevar (*(pd: pi_dom)*) := {
  v_typevar : typevar -> sort;
  (*All sorts must be valid*)
  (*v_typevar_val: forall x, valid_type sigma (v_typevar x);*)
}.*)
Definition val_vars (pd: pi_dom) (vt: val_typevar) : Type :=
  forall (x: vsymbol), domain (dom_aux pd) (v_subst vt (snd x)).

  (*
Record valuation (i: pre_interp) := {
  
  v_vars: forall (x: vsymbol), (domain (dom_aux i) (v_subst (v_typevar) (snd x)))
}.*)

Section Interp.

Variable pd: pi_dom.
Variable pfp: pi_funpred pd.
Variable v: val_typevar.

Notation val t  := (domain (dom_aux pd) (v_subst v t)).

Definition var_to_dom (vv: val_vars pd v) (x: vsymbol): val (snd x) :=
  vv x.

(*Substitution*)

(*Here, a substitution means that we replace a variable of type t
  with an element of [val t]. This affects the valuation v:
  ie: v' := v[x -> y], where y \in [[v(t)]]
  We will prove that, for all tm, [[tm]]_v' = [[tm]]_v.
  We will always be replacing variable 0 in a term (the innermost bound variable)
  *)

Definition substi (vv: val_vars pd v) (x: vsymbol) (y: val (snd x)) : 
  val_vars pd v.
Proof.
  unfold val_vars. intros m.
  destruct (vsymbol_eq_dec m x).
  - rewrite e. exact y.
  - exact (vv m).
Defined.
(*
Print substi.

  fun m =>
    match (vsymbol_eq_dec )

valuation i.
apply (Build_valuation i (v_typevar i v)).
+ exact (v_typevar_val i v).  
+ intros m. destruct (vsymbol_eq_dec m x).
  * subst. exact y.
  * exact (v_vars i v m).
Defined.
*)
Require Import FunctionalExtensionality.

Lemma substi_same (vv: val_vars pd v) (x: vsymbol) (y z: val (snd x)):
  substi (substi vv x y) x z =
  substi vv x z.
Proof.
  unfold substi.
  apply functional_extensionality_dep; intros. 
  destruct (vsymbol_eq_dec x0 x); subst; reflexivity.
Qed.

Lemma substi_diff (vv: val_vars pd v) (x1 x2: vsymbol) y z :
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

(*
  destruct (vty_eq_dec ty ty').
  - subst. apply y.
  - (*trivial case*) apply (v_vars i v m ty').
  - apply (v_vars i v m ty').
Defined.*)

(* Some additional lemmas for casting/dependent type obligations *)
Notation dcast := (dom_cast (dom_aux pd)).

Definition dom_int : domain (dom_aux pd) s_int := 0%Z.

(* Semantics/Interpretation *)

(* We use bools rather than Props to better match the intended semantics in
   in the paper. As a bonus, we get proof irrelevance for free. *)

Definition bool_of_binop (b: binop) : bool -> bool -> bool :=
  match b with
  | Tand => andb
  | Tor => orb
  | Timplies => implb
  | Tiff => eqb
  end.


(*Build valuation from a list, ie: the valuation that sends each element of vs
  to the corresponding sort in s and each element of syms to the
  corresponding element of a (modulo dependent type stuff)
  Give default values if something is not in the list*)

  Set Bullet Behavior "Strict Subproofs".

Lemma make_val_valid_type: forall (vs: list typevar) (s1: list sort),
  length vs = length s1 ->
  (forall s, In s s1 -> valid_type sigma s) ->
  forall (x: typevar), valid_type sigma (ty_subst_fun_s vs s1 s_int x).
Proof.
  intros vs s1 Hlen Hall. unfold ty_subst_fun_s. simpl.
  assert (length vs = length (sorts_to_tys s1)). {
    unfold sorts_to_tys; rewrite map_length; auto.
  }
  (*Should be separate lemma*)
  assert (forall x, In x (sorts_to_tys s1) -> valid_type sigma x). {
    intros. unfold sorts_to_tys in H0. rewrite in_map_iff in H0.
    destruct H0 as [y [Hy Hiny]]; subst. apply Hall. auto.
  }
  clear Hall Hlen. generalize dependent vs.
  induction (sorts_to_tys s1); intros.
  - destruct vs ;[|inversion H]. constructor.
  - destruct vs;[inversion H|]. simpl.
    destruct (typevar_eq_dec x t).
    + subst. apply H0. left; auto.
    + apply IHl; auto. intros. apply H0; right; auto.
Qed.

  (*
Unset Elimination Schemes.
Inductive term_interp: 
  forall (vv: val_vars pd v) (tm: term) (ty: vty) (x: domain (dom_aux pd) (v_subst (v_typevar v) ty)), Prop :=
  | TI_int: forall v z,
    term_interp v (Tconst (ConstInt z)) vty_int z
  | TI_real: forall v r,
    term_interp v (Tconst (ConstReal r)) vty_real r
  | TI_var: forall v (x: vsymbol),
    term_interp v (Tvar x) (snd x) (var_to_dom v x)
  | TI_iftrue: forall v f t1 t2 ty x,
    formula_interp v nil nil f true -> (*TODO: does empty work?*)
    term_interp v t1 ty x ->
    term_interp v (Tif f t1 t2) ty x
  | TI_iffalse: forall v f t1 t2 ty x,
    formula_interp v nil nil f false ->
    term_interp v t2 ty x ->
    term_interp v (Tif f t1 t2) ty x
  (*substitution changes the valuation *)
  | TI_let: forall v t1 (x: vsymbol) t2 ty2 x1 x2,
    term_interp v t1 (snd x) x1 ->
    term_interp (substi v x x1) t2 ty2 x2 ->
    term_interp v (Tlet t1 x t2) ty2 x2
  | TI_func: forall (vv: val_vars pd v) (f: funsym) (params: list vty) (ts: list term) 
    (Hlen: length (s_params f) = length params) xs,

    let v_map := v_subst (v_typevar v) in
    (* First, we get the interpretation of f *)
    let f_interp := (funs pd pfp) f (map v_map params)  in
    (* Return type of f (sigma(s_ret f))*)
    let f_ret := (funsym_sigma_ret f (map v_map params)) in
    (*Now we need to apply it to the arguments*)
    (*argument ts_i has type sigma((s_args f)_i), where sigma is
      the map that sends the function params alpha_i -> v(params_i).
      This means that all of these types are sorts, so v(sigma(s_args f)_i) =
      sigma((s_args f)_i). Therefore, if [[t_i]]_v = x_i, x_i has the correct
      type to pass into f_interp. However, we need manual casting in Coq
      and this gets quite ugly. *)

    (*The list of sigma(s_args)_i*)
    let f_arg_typs : list sort :=
      funsym_sigma_args f (map v_map params) in

    (*ith elt of xs is [[t_i]]_v. We need to cast the types to get the type as
      [[v(sigma(s_args f)_i)]]*)
    (* We give 0 and s_int as the default term and sort, respectively. This is
       arbitrary and doesn't matter, our length assumptions ensures everything is
       within bounds.*)
    (forall n (Hn: n < length f_arg_typs),
      (*Ignoring dependent type obligations/casting, this says that:
        For all n in bounds, [nth n ts] (of type [nth n f_args_typs]) 
        evaluates to [nth xs n] under v *)
      term_interp vv (nth n ts (Tconst (ConstInt 0)))
        (nth n f_arg_typs s_int) 
        (dcast (subst_sort_eq (nth n f_arg_typs s_int) (v_typevar v)) 
          (hnth n xs s_int dom_int))) ->
    
    (*Again, we must cast the return type of f, for the same reason*)
    term_interp vv (Tfun f params ts) f_ret 
      (dcast (subst_sort_eq f_ret (v_typevar v)) (f_interp xs))
  | TI_match: forall v (t: term) ty1 ty (ps: list (pattern * term)) (t': term) x,
    (*Translate the pattern match to a term of tests (with match_pattern), then
      interpret*)
    match_pattern term Tlet v t (map fst ps) (map snd ps) (Some t') ->
    term_interp v t' ty x ->
    term_interp v (Tmatch t ty1 ps) ty x

with formula_interp: (val_vars pd v) -> list formula -> list formula -> formula -> bool -> Prop :=
  | FI_true: forall v tl fl, formula_interp v tl fl Ftrue true
  | FI_false: forall v tl fl, formula_interp v tl fl Ffalse false
  | FI_not: forall v tl fl f b,
    formula_interp v tl fl f b ->
    formula_interp v tl fl (Fnot f) (negb b)
  | FI_binop: forall v b f1 f2 b1 b2 tl fl,
    formula_interp v tl fl f1 b1 ->
    formula_interp v tl fl f2 b2 ->
    formula_interp v tl fl (Fbinop b f1 f2) (bool_of_binop b b1 b2)
  | FI_iftrue: forall v f f1 f2 b tl fl,
    formula_interp v tl fl f true ->
    formula_interp v tl fl f1 b ->
    formula_interp v tl fl (Fif f f1 f2) b
  | FI_iffalse: forall v f f1 f2 b tl fl,
    formula_interp v tl fl f false ->
    formula_interp v tl fl f2 b ->
    formula_interp v tl fl (Fif f f1 f2) b
  | FI_let: forall v t (x: vsymbol) f x1 b tl fl,
    term_interp v t (snd x) x1 ->
    formula_interp (substi v x x1) tl fl f b ->
    formula_interp v tl fl (Flet t x f) b
  | FI_forallT: forall v x f tl fl,
    (forall d, formula_interp (substi v x d) tl fl f true) ->
    formula_interp v tl fl (Fquant Tforall x f) true
  (*TODO: may not need this with classical part*)
  | FI_forallF: forall v x f d tl fl, (*otherwise we cannot prove that forall is false*)
    (formula_interp (substi v x d) tl fl f false) ->
    formula_interp v tl fl (Fquant Tforall x f) false
  | FI_existsT: forall v x f d tl fl,
    (formula_interp (substi v x d) tl fl f true) ->
    formula_interp v tl fl (Fquant Texists x f) true
  | FI_existsF: forall v x f tl fl,
    (forall d, formula_interp (substi v x d) tl fl f false) ->
    formula_interp v tl fl (Fquant Texists x f) false
  | FI_eqT: forall v ty t1 t2 x1 x2 tl fl, (*TODO: assume decidable equality?*)
    term_interp v t1 ty x1 ->
    term_interp v t2 ty x2 ->
    x1 = x2 ->
    formula_interp v tl fl (Feq ty t1 t2) true
  (*TODO: may not need this also (or assume decidable)*)
  | FI_eqF: forall v ty t1 t2 x1 x2 tl fl,
    term_interp v t1 ty x1 ->
    term_interp v t2 ty x2 ->
    x1 <> x2 ->
    formula_interp v tl fl (Feq ty t1 t2) false
  | FI_prop: forall (vv: val_vars pd v) (p: predsym) (params: list vty) (ts: list term) 
    (Hlen: length (p_params p) = length params) xs tl fl,

    (*Very similar to function*)

    let v_map := v_subst (v_typevar v) in
    (* First, we get the interpretation of p *)
    let p_interp := (preds pd pfp) p (map v_map params)  in
    (*let f_ret := (funsym_sigma_ret f (map v_map params) 
      (map_length_eq v_map _ _ Hlen)) in*)

    (*The list of sigma(s_args)_i*)
    let p_arg_typs : list sort :=
      predsym_sigma_args p (map v_map params) in
    (*ith elt of xs is [[t_i]]_v. We need to cast the types to get the type as
      [[v(sigma(s_args f)_i)]]*)

    (forall n (Hn: n < length p_arg_typs),
      term_interp vv (nth n ts (Tconst (ConstInt 0)))
        (nth n p_arg_typs s_int) 
        (dcast (subst_sort_eq (nth n p_arg_typs s_int) (v_typevar v)) 
          (hnth n xs s_int dom_int ))) ->

    formula_interp vv tl fl (Fpred p params ts) (p_interp xs)
  | FI_match: forall v (t: term) ty (ps: list (pattern * formula)) (f: formula) b tl fl,
    (*Translate the pattern match to a formula of tests (with match_pattern), then
      interpret*)
    match_pattern formula Flet v t (map fst ps) (map snd ps) (Some f) ->
    formula_interp v tl fl f b ->
    formula_interp v tl fl (Fmatch t ty ps) b
  (* Make the logic classical *)
  | FI_VarT: forall v f tl fl,
    In f tl ->
    formula_interp v tl fl f true
  | FI_VarF: forall v f tl fl,
    In f fl ->
    formula_interp v tl fl f false
  | FI_ActT: forall v f f' tl fl,
    formula_interp v tl (f :: fl) f' true ->
    formula_interp v tl (f :: fl) f' false ->
    formula_interp v tl fl f true
  | FI_ActF: forall v f f' tl fl,
    formula_interp v (f :: tl) fl f' true ->
    formula_interp v (f :: tl) fl f' false ->
    formula_interp v tl fl f false

  (*Add bool so that we can say: not proj_constr*)
  (*Similar to projf_{i, j} in the paper, but gives whole list if 
    [[t]]]is application of [[f]] to [[ts]]*)
with proj_constr : (val_vars pd v) -> term -> funsym -> list vty -> list term -> bool -> Prop :=
| mk_proj_constr: forall v t ty f vs ts x y,
    term_interp v t ty x ->
    term_interp v (Tfun f vs ts) ty y ->
    x = y ->
    (*Says that [[t]] = [[f(vs)]][[ts]], but operation on t and ts (NOT interpretations)*)
    proj_constr v t f vs ts true
| not_proj_constr: forall v ty f vs ts x t' x',
    term_interp v (Tfun f vs ts) ty x ->
    term_interp v t' ty x' ->
    x <> x' ->
    proj_constr v t' f vs ts false
(*We define [is_constr] as (exists tm, proj_constr v t f vs ts true) and
  not [is_constr] is (forall tm, proj_constr v t f vs ts false)*)

  (*pattern interpretations are almost the same for terms and formulas; the
    only difference being that one takes in/returns a term, and the other a formula
    (using Tlet/Flet). So we factor out the difference and pass in the appropriate
    type in the term/formula interpretation*)
  with pattern_interp: forall (A: Type) (flet: term -> vsymbol -> A -> A),
     (val_vars pd v) ->term -> pattern -> option A -> option A -> option A -> Prop :=
  | PI_varNone: forall A flet v t x h,
    pattern_interp A flet v t (Pvar x) None h None
  | PI_varSome: forall A flet v t x b h,
    pattern_interp A flet v t (Pvar x) (Some b) h (Some (flet t x b))
  | PI_constrNilT: forall A flet (vv: val_vars pd v) t (f: funsym) (vs: list vty) b h,
    (*If the interpretation of t (ie x), comes from the constructor f: *)
    (exists ts, proj_constr vv t f vs ts true) ->

    pattern_interp A flet vv t (Pconstr f vs nil) b h b
  | PI_constrF: forall A flet v t (f: funsym) (vs: list vty) (ps: list pattern) b h,
    (*If the interpretation of x does not come from the constructor f*)
    (forall ts, proj_constr v t f vs ts false) ->

    pattern_interp A flet v t (Pconstr f vs ps) b h h
  | PI_constrConsT: forall A flet v t f (vs: list vty) (ps: list pattern) 
    b h ts res,
    proj_constr v t f vs ts true ->

    (*more complicated than I thought: need to distinguish between interp and term*)
    iter_pattern_interp A flet v ts ps b h res ->
    pattern_interp A flet v t (Pconstr f vs ps) b h res
  | PI_wild: forall A flet v t b h,
    pattern_interp A flet v t Pwild b h b
  | PI_or: forall A flet v t p1 p2 b h res res1,
    pattern_interp A flet v t p2 b h res ->
    pattern_interp A flet v t p1 b res res1 ->
    pattern_interp A flet v t (Por p1 p2) b h res1
  | PI_bindNil: forall A flet v t p x b h,
    pattern_interp A flet v t p b h None ->
    pattern_interp A flet v t (Pbind p x) b h None
  | PI_bind: forall A flet v t p x b h res,
    pattern_interp A flet v t p b h (Some res) ->
    pattern_interp A flet v t (Pbind p x) b h (Some (flet t x res))

with iter_pattern_interp: forall (A: Type) (flet: term -> vsymbol -> A -> A),
(val_vars pd v) -> list term -> list pattern -> option A -> option A -> option A -> Prop :=
  | IPI_nil:
    forall A flet v b h,
    iter_pattern_interp A flet v nil nil b h b
  | IPI_cons: forall A flet v t ts p ps b h res res1,
    iter_pattern_interp A flet v ts ps b h res ->
    pattern_interp A flet v t p res h res1 ->
    iter_pattern_interp A flet v (t :: ts) (p :: ps) b h res1

(*We need another form of iteration, where failures are propagated*)
with match_pattern: forall (A: Type) (flet: term -> vsymbol -> A -> A),
  (val_vars pd v) -> term -> list pattern -> list A -> option A -> Prop :=
  | MP_nil: forall A flet v t,
    match_pattern A flet v t nil nil None
  | MP_cons: forall A flet v t p ps tm ts res res1,
    match_pattern A flet v t ps ts res ->
    pattern_interp A flet v t p (Some tm) res res1 ->
    match_pattern A flet v t (p :: ps) (tm :: ts) res1.
Set Elimination Schemes.

Scheme term_interp_ind := Minimality for term_interp Sort Prop
with formula_interp_ind := Minimality for formula_interp Sort Prop
with proj_constr_ind := Minimality for proj_constr Sort Prop
with pattern_interp_ind := Minimality for pattern_interp Sort Prop
with iter_pattern_interp_ind := Minimality for iter_pattern_interp Sort Prop
with match_pattern_ind := Minimality for match_pattern Sort Prop.

(* Tests/Examples *)

(*Our rules for quantifiers are OK constructively*)

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

(*The bool version of [proj_constr] works*)
(*
Lemma proj_constr_false: forall v t f vs ts,
  proj_constr v t f vs ts false ->
  ~ proj_constr v t f vs ts true.
Proof.
  intros. intro C. inversion H; subst.
  inversion C; subst. (*need injectivity, but true*)
Abort.

Lemma proj_constr_false': forall v t f vs,
  (forall ts, proj_constr v t f vs ts false) ->
  ~ (exists ts, proj_constr v t f vs ts true).
Proof.
  intros. intro C. destruct C as [ts Hp].
  specialize (H ts). (*previous "lemma"*)
Abort.*)

Section Ex.

Local Open Scope string_scope.
(*Let's give an example: prove that equality is reflexive*)
Lemma prove_eq_refl: forall (vv: val_vars pd v) (a: vty) tl fl,
  formula_interp vv tl fl (Fquant Tforall ("x", a) (Feq a (Tvar ("x", a)) (Tvar ("x", a)))) true.
Proof.
  intros vv a. constructor. intros d.
  eapply FI_eqT. 
  - apply TI_var.
  - apply TI_var.
  - reflexivity. 
Qed.

End Ex.

End Interp.

(* Some results about interpretations *)
Section InterpLemmas.

(*There is always a trivial valuation (need for defaults)*)
Definition triv_val_typevar (*(pd: pi_dom) (i: pre_interp)*) : val_typevar.
Proof.
  apply (Build_val_typevar (fun _ => s_int)).
  intros. constructor.
Defined.

Definition triv_val_vars (i: pi_dom) : val_vars i (triv_val_typevar).
Proof.
  unfold val_vars. intros x.
  destruct i; simpl. unfold v_subst.
  specialize (domain_ne0 (v_subst (fun _ : typevar => s_int) (snd x))).
  inversion domain_ne0. exact x0.
Defined.

Ltac interp_TF :=
  match goal with
  | [H1: forall b: bool, formula_interp ?i ?v ?f b -> true = b,
    H2: formula_interp ?i ?v ?f1 false |- _ ] => apply H1 in H2; inversion H2
  | [H1: forall b:bool, formula_interp ?i ?v ?f b -> false = b,
    H2: formula_interp ?i ?v ?f1 true |- _] => apply H1 in H2; inversion H2
    end.

Lemma nat_eq_irrel: forall {n m: nat} (H1 H2: n = m), H1 = H2.
Proof.
  apply UIP_dec. apply Nat.eq_dec.
Qed.

(* An important theorem: our evaluation mechanism is deterministic: each
  term and formula evaluate to only one answer. We need to use our
  mutually recursive induction principle for this, so we actually prove
  both results simultaneously*)
(*
  Lemma formula_interp_det: forall i v f b1 b2,
  formula_interp i v f b1 ->
  formula_interp i v f b2 ->
  b1 = b2.
Proof.
    intros i v f b1 b2 H C. generalize dependent b2. revert H.
    apply (formula_interp_ind i (fun (v: valuation i) (t: term) (ty: vty)
      (x: domain i (v_subst (v_typevar i v) ty)) =>
      (forall x2, term_interp i v t ty x2 -> x = x2))
      (fun (v: valuation i) (f: formula) (b: bool) =>
        (forall b2, formula_interp i v f b2 -> b = b2))); intros;
    try solve[dependent destruction H; reflexivity].
    + dependent destruction H3; auto.
      interp_TF.
    + dependent destruction H3; auto.
      interp_TF.
    + dependent destruction H3; auto.
      apply H0 in H3_; subst.
      apply H2 in H3_0; auto.
    + dependent destruction H1; auto.
      subst f_interp. subst f_interp0. subst v_map. subst v_map0.
      assert (Hlen = Hlen0) by (apply nat_eq_irrel).
      subst. f_equal. f_equal. 
      (*need to know that each individual elt equal, so whole is
        need eq_ext for arg_list*)
      apply arg_list_eq_ext with(d:=s_int)(d':=dom_int i). intros n Hn.
      specialize (H1 n Hn). specialize (H n Hn).
      specialize (H0 n Hn _ H1). apply dom_cast_inj in H0. auto.
    + dependent destruction H1. rewrite (H0 _ H1). reflexivity.
    + dependent destruction H3.
      apply H0 in H3_; subst. apply H2 in H3_0; subst. reflexivity.
    + dependent destruction H3; auto. interp_TF.
    + dependent destruction H3; auto. interp_TF.
    + dependent destruction H3; auto. apply H0 in H3; subst.
      apply H2 in H4. auto.
    + dependent destruction H1; auto.
      apply H0 in H1. auto.
    + dependent destruction H1; auto.
    + dependent destruction H1; auto.
    + dependent destruction H1; auto.
      apply H0 in H1; auto.
    + dependent destruction H4; auto; subst.
      apply H0 in H4; subst. apply H2 in H5; subst. contradiction.
    + dependent destruction H4; auto; subst.
      apply H0 in H4; apply H2 in H5; subst; contradiction.
    + dependent destruction H1; auto.
      subst p_interp. subst p_interp0. subst v_map. subst v_map0.
      assert (Hlen = Hlen0) by (apply nat_eq_irrel).
      subst. f_equal. 
      apply arg_list_eq_ext with(d:=s_int)(d':=dom_int i). intros n Hn.
      specialize (H1 n Hn). specialize (H n Hn).
      specialize (H0 n Hn _ H1). apply dom_cast_inj in H0. auto.
Qed.

(*TODO: how to avoid repetition, exact same proof*)
Lemma term_interp_det: forall i v t ty x1 x2,
  term_interp i v t ty x1 ->
  term_interp i v t ty x2 ->
  x1 = x2.
Proof.
  intros i v t ty x1 x2 H C. generalize dependent x2. revert H.
  apply (term_interp_ind i (fun (v: valuation i) (t: term) (ty: vty)
    (x: domain i (v_subst (v_typevar i v) ty)) =>
    (forall x2, term_interp i v t ty x2 -> x = x2))
    (fun (v: valuation i) (f: formula) (b: bool) =>
      (forall b2, formula_interp i v f b2 -> b = b2))); intros;
  try solve[dependent destruction H; reflexivity].
  + dependent destruction H3; auto.
    interp_TF.
  + dependent destruction H3; auto.
    interp_TF.
  + dependent destruction H3; auto.
    apply H0 in H3_; subst.
    apply H2 in H3_0; auto.
  + dependent destruction H1; auto.
    subst f_interp. subst f_interp0. subst v_map. subst v_map0.
    assert (Hlen = Hlen0) by (apply nat_eq_irrel).
    subst. f_equal. f_equal. 
    (*need to know that each individual elt equal, so whole is
      need eq_ext for arg_list*)
    apply arg_list_eq_ext with(d:=s_int)(d':=dom_int i). intros n Hn.
    specialize (H1 n Hn). specialize (H n Hn).
    specialize (H0 n Hn _ H1). apply dom_cast_inj in H0. auto.
  + dependent destruction H1. rewrite (H0 _ H1). reflexivity.
  + dependent destruction H3.
    apply H0 in H3_; subst. apply H2 in H3_0; subst. reflexivity.
  + dependent destruction H3; auto. interp_TF.
  + dependent destruction H3; auto. interp_TF.
  + dependent destruction H3; auto. apply H0 in H3; subst.
    apply H2 in H4. auto.
  + dependent destruction H1; auto.
    apply H0 in H1. auto.
  + dependent destruction H1; auto.
  + dependent destruction H1; auto.
  + dependent destruction H1; auto.
    apply H0 in H1; auto.
  + dependent destruction H4; auto; subst.
    apply H0 in H4; subst. apply H2 in H5; subst. contradiction.
  + dependent destruction H4; auto; subst.
    apply H0 in H4; apply H2 in H5; subst; contradiction.
  + dependent destruction H1; auto.
    subst p_interp. subst p_interp0. subst v_map. subst v_map0.
    assert (Hlen = Hlen0) by (apply nat_eq_irrel).
    subst. f_equal. 
    apply arg_list_eq_ext with(d:=s_int)(d':=dom_int i). intros n Hn.
    specialize (H1 n Hn). specialize (H n Hn).
    specialize (H0 n Hn _ H1). apply dom_cast_inj in H0. auto.
Qed.
*)
End InterpLemmas.

(*Find element of arg_list corresponding to element of l*)
(*This is very ugly due to dependent types and proof obligations*)
Fixpoint mk_fun_arg (*{A: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})*) 
  (pd: pi_dom) v_var
  (l: list vsymbol) (s: list sort) (a: arg_list (domain (dom_aux pd)) s) 
    (x: vsymbol): 
    domain (dom_aux pd) (v_subst v_var (snd x)) :=
  match l, a with
  | hd :: tl, HL_cons shd stl d t => 
      (*Need to know that types are equal so we can cast the domain*)
      match (vty_eq_dec (v_subst v_var (snd x))) shd with
      | left Heq => if vsymbol_eq_dec hd x then dom_cast _ (sort_inj (eq_sym Heq)) d
          else mk_fun_arg pd v_var tl stl t x
      | _ => mk_fun_arg pd v_var tl stl t x
      end
  (* Otherwise, return default element of domain *)
  | _, _ =>  match domain_ne pd (v_subst v_var (snd x)) with
                      | DE y => y
                      end
  end.


Definition make_val_typevar (*(pd: pi_dom)*) (vs: list typevar) (s1 (*s2*): list sort)
  (Hlen: length vs = length s1)
  (Hall: forall s, In s s1 -> valid_type sigma s)
  (*(syms: list vsymbol)*) (*(a: arg_list (domain (dom_aux pd)) s2)*) : val_typevar :=
  let v_var := (ty_subst_fun_s vs s1 s_int) in
  Build_val_typevar v_var (make_val_valid_type vs s1 Hlen Hall).

Definition make_val_vars (pd: pi_dom) (vs: list typevar) (s1 s2: list sort)
  (Hlen: length vs = length s1)
  (Hall: forall s, In s s1 -> valid_type sigma s)
  (syms: list vsymbol) (a: arg_list (domain (dom_aux pd)) s2) : 
    val_vars pd (make_val_typevar vs s1 Hlen Hall) :=
  let v_var := (ty_subst_fun_s vs s1 s_int) in
  (mk_fun_arg pd v_var syms s2 a).

(* Interpretation, Satisfiability, Validity *)

Section Logic.


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

End Interp.