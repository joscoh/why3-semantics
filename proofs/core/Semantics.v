Require Import Types.
Require Import Syntax.

(** Semantics **)

Fixpoint curry (l: list Type) (ret: Type) : Type :=
  match l with
  | nil => ret
  | x :: t => x -> (curry t ret)
  end.

(*Here, we prove that a type substitution that replaces all of the type
  parameters for a function/pred symbol with sorts results in a sort *)
Definition subst_funsym_params (f: funsym) (s: list sort) 
  (Hlen: length (s_params f) = length s): list sort :=
  ty_subst_list_s (s_params f) s Hlen (s_args f) (s_args_wf f).

Definition subst_predsym_params (p: predsym) (s: list sort)
  (Hlen: length (p_params p) = length s) : list sort :=
  ty_subst_list_s (p_params p) s Hlen (p_args p) (p_args_wf p).

Record pre_interp := {
  domain: sort -> Type;
  domain_int: domain s_int = Z;
  domain_real: domain s_real = R;

  (*This is quite unwieldy (and could be wrong) - need to see if works/can do better*)

  funs: forall (f:funsym) (s: list sort) (Hlen: length (s_params f) = length s),
    curry (map domain (subst_funsym_params f s Hlen))
      (domain (ty_subst_s (s_params f) s Hlen (s_ret f) (s_ret_wf f)));
  preds: forall (p:predsym) (s: list sort) (Hlen: length (p_params p) = length s),
    curry (map domain (subst_predsym_params p s Hlen))
      Prop
}.

(*Substitute according to function*)
Fixpoint v_subst_aux (v: typevar -> sort) (t: vty) : vty :=
  match t with
  | vty_int => vty_int
  | vty_real => vty_real
  | vty_var tv => v tv
  | vty_cons ts vs => vty_cons ts (map (v_subst_aux v) vs)
  end.

Lemma v_subst_aux_sort: forall v t,
  is_sort (v_subst_aux v t).
Proof.
  intros v t. unfold is_sort.
  assert (H: type_vars (v_subst_aux v t) = nil); [|rewrite H; auto].
  induction t; simpl; intros; auto.
  apply sort_type_vars.
  induction vs; simpl; intros; auto.
  inversion H; subst.
  rewrite H2. auto.
Qed. 

Definition v_subst (v: typevar -> sort) (t: vty) : sort :=
  exist _ (v_subst_aux v t) (v_subst_aux_sort v t).

(*Valuations*)
Record valuation (i: pre_interp) := {
  v_typevar : typevar -> sort;
  v_vars: forall (n: nat) (v: vty), (domain i (v_subst (v_typevar) v))
}.

Section Interp.

Variable i: pre_interp.

Definition val (v: valuation i) t : Type := domain i (v_subst (v_typevar i v) t).

Definition z_to_dom (v: valuation i) (z: Z) : val v vty_int.
Proof.
  unfold val. erewrite sort_inj. rewrite (domain_int i). apply z.
  reflexivity.
Defined.

Definition r_to_dom (v: valuation i) (r: R) : val v vty_real.
Proof.
  unfold val. erewrite sort_inj. rewrite (domain_real i). apply r.
  reflexivity.
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

(* We use bools rather than Props to better match the intended semantics in
   in the paper. As a bonus, we get proof irrelevance for free. *)

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
  (*| TI_func: forall v (f: funsym) (params: list vty) (ts: list term) ty xs x,
    let tys := ty_subst_list (s_params f) params  
    Forall (fun x => term_interp v (fst x) (snd x)) (combine (combine (s_args ) ts xs) ->
    term_interp v *)
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

End Interp.