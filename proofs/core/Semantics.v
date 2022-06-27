Require Import Types.
Require Import Syntax.

(** Semantics **)

(*A custom list-like data type which holds values of types [[s_i]], where
    s is a list of sorts*)
Inductive arg_list (domain: sort -> Type) : list sort -> Type :=
  | AL_nil: arg_list domain nil
  | AL_cons: forall s tl,
      domain s ->
      arg_list domain tl ->
      arg_list domain (s :: tl).

(*Some definitions on [arg_list]*)
Fixpoint arg_length {domain: sort -> Type} {l: list sort} (a: arg_list domain l) : nat :=
  match a with
  | AL_nil _ => 0
  | AL_cons _ _ _ d tl => 1 + arg_length tl
  end.

Lemma arg_length_sorts: forall (domain: sort -> Type) (l: list sort) (a: arg_list domain l),
  arg_length a = length l.
Proof.
  intros d l a. induction a; simpl; auto.
Qed.

Definition arg_nth {domain: sort -> Type} {l: list sort} (a: arg_list domain l) (i: nat)
  (Hi: i < length l) (d: sort) : domain (nth i l d).
Proof.
  rewrite <- (arg_length_sorts domain l a) in Hi.
  generalize dependent i. induction a; simpl; intros.
  - exfalso. apply (Nat.nlt_0_r i). apply Hi.
    (*not using lia because it might be hard to compute*) 
  - destruct i.
    + simpl. apply d0.
    + apply IHa. apply lt_S_n, Hi.
Defined.

(*Here, we prove that a type substitution that replaces all of the type
  parameters for a function/pred symbol with sorts results in a sort *)
Definition funsym_sigma_args (f: funsym) (s: list sort) 
  (Hlen: length (s_params f) = length s): list sort :=
  ty_subst_list_s (s_params f) s Hlen (s_args f) (s_args_wf f).

Definition funsym_sigma_ret (f: funsym) (s: list sort)
(Hlen: length (s_params f) = length s) : sort :=
  ty_subst_s (s_params f) s Hlen (s_ret f) (s_ret_wf f).

Definition predsym_sigma_args (p: predsym) (s: list sort)
  (Hlen: length (p_params p) = length s) : list sort :=
  ty_subst_list_s (p_params p) s Hlen (p_args p) (p_args_wf p).

Record pre_interp := {
  domain: sort -> Type;
  domain_int: domain s_int = Z;
  domain_real: domain s_real = R;

  (*This is quite unwieldy (and could be wrong) - need to see if works/can do better*)

  funs: forall (f:funsym) (s: list sort) (Hlen: length (s_params f) = length s),
    arg_list domain (funsym_sigma_args f s Hlen) ->
    (domain (funsym_sigma_ret f s Hlen));

  preds: forall (p:predsym) (s: list sort) (Hlen: length (p_params p) = length s),
    arg_list domain (predsym_sigma_args p s Hlen) -> bool
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

(* Some additional lemmas for casting/dependent type obligations *)

Lemma map_length_eq: forall {A B C: Type} (f: B -> C) (l1 : list A) (l2 : list B),
  length l1 = length l2 ->
  length l1 = length (map f l2).
Proof.
  intros. rewrite H, map_length. reflexivity.
Qed.

(* If we have a sort, then substituting a valuation does nothing *)
Lemma subst_sort_eq: forall (s: sort) (v: typevar -> sort),
  s = v_subst v (sort_to_ty s).
Proof.
  intros. unfold v_subst. destruct s.
  induction x; simpl; auto; try solve[apply sort_inj; reflexivity].
  - apply sort_inj; simpl. unfold is_sort in i0. simpl in i0. inversion i0.
  - rewrite Forall_forall in H. apply sort_inj; simpl.
    f_equal. apply list_eq_ext'; try rewrite !map_length; auto.
    intros n d Hn. rewrite map_nth_inbound with(d2:=d); auto.
    assert (Hin: In (nth n vs d) vs) by (apply nth_In; auto).
    assert (Hsort: is_sort (nth n vs d)). {
      unfold is_sort. unfold is_sort in i0.
      rewrite (type_vars_cons tsym vs); auto. 
      destruct (type_vars (vty_cons tsym vs)) eqn : Ht; auto. inversion i0.
    }
    specialize (H _ Hin Hsort). inversion H. reflexivity.
Qed. 

(*Cast 1 domain into another*)
Definition dom_cast (v1 v2: sort) (Hv: v1 = v2) (x: domain i v1) : domain i v2.
subst. apply x.
Defined.


(* Semantics/Interpretation *)

(*TODO: is the underlying logic supposed to be classical or constructive?
  Seemingly classical in paper because formula interpretations are equal to bool.
  We can assume LEM and write a function to evaluate a term/formula instead, 
  should we do this?*)

(* We use bools rather than Props to better match the intended semantics in
   in the paper. As a bonus, we get proof irrelevance for free. *)

Definition bool_of_binop (b: binop) : bool -> bool -> bool :=
  match b with
  | Tand => andb
  | Tor => orb
  | Timplies => implb
  | Tiff => eqb
  end.

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
  | TI_func: forall (v: valuation i) (f: funsym) (params: list vty) (ts: list term) 
    (Hlen: length (s_params f) = length params) xs,

    let v_map := v_subst (v_typevar i v) in
    (* First, we get the interpretation of f *)
    let f_interp := (funs i) f (map v_map params) 
      (map_length_eq v_map _ _ Hlen) in
    (* Return type of f (sigma(s_ret f))*)
    let f_ret := (funsym_sigma_ret f (map v_map params) 
      (map_length_eq v_map _ _ Hlen)) in
    (*Now we need to apply it to the arguments*)
    (*argument ts_i has type sigma((s_args f)_i), where sigma is
      the map that sends the function params alpha_i -> v(params_i).
      This means that all of these types are sorts, so v(sigma(s_args f)_i) =
      sigma((s_args f)_i). Therefore, if [[t_i]]_v = x_i, x_i has the correct
      type to pass into f_interp. However, we need manual casting in Coq
      and this gets quite ugly. *)

    (*The list of sigma(s_args)_i*)
    let f_arg_typs : list sort :=
      funsym_sigma_args f (map v_map params) (map_length_eq v_map _ _ Hlen) in

    (*ith elt of xs is [[t_i]]_v. We need to cast the types to get the type as
      [[v(sigma(s_args f)_i)]]*)
    (* We give 0 and s_int as the default term and sort, respectively. This is
       arbitrary and doesn't matter, our length assumptions ensures everything is
       within bounds.*)
    (forall n (Hn: n < length f_arg_typs),
      (*Ignoring dependent type obligations/casting, this says that:
        For all n in bounds, [nth n ts] (of type [nth n f_args_typs]) 
        evaluates to [nth xs n] under v *)
      term_interp v (nth n ts (Tconst (ConstInt 0)))
        (nth n f_arg_typs s_int) 
        (dom_cast _ _ (subst_sort_eq (nth n f_arg_typs s_int) (v_typevar i v)) 
          (@arg_nth _ f_arg_typs xs n Hn s_int))) ->
    
    (*Again, we must cast the return type of f, for the same reason*)
    term_interp v (Tfun f params ts) f_ret 
      (dom_cast _ _ (subst_sort_eq f_ret (v_typevar i v)) (f_interp xs))

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
  | FI_prop: forall (v: valuation i) (p: predsym) (params: list vty) (ts: list term) 
    (Hlen: length (p_params p) = length params) xs,

    (*Very similar to function*)

    let v_map := v_subst (v_typevar i v) in
    (* First, we get the interpretation of p *)
    let p_interp := (preds i) p (map v_map params) 
      (map_length_eq v_map _ _ Hlen) in
    (*let f_ret := (funsym_sigma_ret f (map v_map params) 
      (map_length_eq v_map _ _ Hlen)) in*)

    (*The list of sigma(s_args)_i*)
    let p_arg_typs : list sort :=
      predsym_sigma_args p (map v_map params) (map_length_eq v_map _ _ Hlen) in
    (*ith elt of xs is [[t_i]]_v. We need to cast the types to get the type as
      [[v(sigma(s_args f)_i)]]*)

    (forall n (Hn: n < length p_arg_typs),
      term_interp v (nth n ts (Tconst (ConstInt 0)))
        (nth n p_arg_typs s_int) 
        (dom_cast _ _ (subst_sort_eq (nth n p_arg_typs s_int) (v_typevar i v)) 
          (@arg_nth _ p_arg_typs xs n Hn s_int))) ->

    formula_interp v (Fpred p params ts) (p_interp xs)
    .

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