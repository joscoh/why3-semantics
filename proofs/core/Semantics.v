Require Import Types.
Require Import Syntax.
Require Import Typing.

Require Import Coq.Program.Equality.
Require Import Coq.Logic.Eqdep_dec.


(** Semantics **)

(* Pattern matching interpretations *)

(*TODO: In the paper, isf_i(t) and similar are defined on interpretations, not
  terms, BUT they use the function on terms in the pattern matching definition.
  So I believe this function should be OK (because on terms, it is decidable)*)
Definition is_constr (f: funsym) (vs: list vty) (t: term) : option (list term) :=
  match t with
  | Tfun f' vs' tms => if funsym_eq_dec f f' && list_eq_dec vty_eq_dec vs vs' then
                        Some tms else None
  | _ => None
  end.

Section PatternInterp.

Context {A: Type} (flet: term -> vsymbol -> vty -> A -> A).

(*A function to compile the compiled version (None is error state).
  This shows compilation actually is decidable, and it makes iteration easier*)
Fixpoint compile_match 
  (t: term) (p: pattern) (b: option A) (h: option A) {struct p} : option A :=
  match p with
  | Pvar x ty => 
    match b with
    | Some tm => Some (flet t x ty tm)
    | None => None
    end
  | Pconstr f vs ps =>
    match ps with
    | nil => 
      match (is_constr f vs t) with
      | Some _ => b
      | None => h
      end
    | _ :: _ =>
      match (is_constr f vs t) with
      | Some ts => 
        ((fix compile_matches (tms: list term) (pats: list pattern) {struct pats} : option A :=
          match tms, pats with
          | nil, nil => b
          | (tm :: tl1), (p1 :: tl2) =>
            compile_match tm p1 (compile_matches tl1 tl2) h
          | _, _ => None
          end
        ) ts ps)
      | None => h
      end
    end
  | Pwild => b
  | Por p1 p2 => compile_match t p1 b (compile_match t p2 b h)
  | Pbind p1 x ty => 
    match (compile_match t p1 b h) with
    | Some tm => Some (flet t x ty tm)
    | None => None
    end
  end.

(*Compile a list of (match, A) pairs where failures are propagated*)
Definition compile_full_match (t: term) (ps: list pattern) (res: list A) : option A :=
  fold_right (fun x acc => compile_match t (fst x) (snd x) acc) None (combine ps (map Some res)).

(* Inductive relation *)

Definition is_some {A: Type} (o: option A) :=
  match o with
  | Some _ => true
  | _ => false
  end.

(*option represents "error", which should never occur in well-typed (exhaustive) pattern*)
(*TODO: prove that we never get error if we have well-typed term*)
(*Their formulation encodes as if statements. We don't do this because isf_i(t) is
  not a valid formula. It may be possible to encode this directly, but it doesn't seem
  necessary.*)
Unset Elimination Schemes.
Inductive pattern_interp : term -> pattern -> option A -> option A -> option A -> Prop :=
  | PI_varNone: forall t x ty h,
    pattern_interp t (Pvar x ty) None h None
  | PI_varSome: forall t x ty b h,
    pattern_interp t (Pvar x ty) (Some b) h (Some (flet t x ty b))
  | PI_constrNilT: forall t (f: funsym) (vs: list vty) b h,
    is_some (is_constr f vs t) ->
    pattern_interp t (Pconstr f vs nil) b h b
  | PI_constrF: forall t (f: funsym) (vs: list vty) (ps: list pattern) b h,
    negb (is_some (is_constr f vs t)) ->
    pattern_interp t (Pconstr f vs ps) b h h
  | PI_constrConsT: forall t f (vs: list vty) (ps: list pattern) b h (ts: list term) res,
    is_constr f vs t = Some ts ->
    iter_pattern_interp ts ps b h res ->
    pattern_interp t (Pconstr f vs ps) b h res
  | PI_wild: forall t b h,
    pattern_interp t Pwild b h b
  | PI_or: forall t p1 p2 b h res res1,
    pattern_interp t p2 b h res ->
    pattern_interp t p1 b res res1 ->
    pattern_interp t (Por p1 p2) b h res1
  | PI_bindNil: forall t p x ty b h,
    pattern_interp t p b h None ->
    pattern_interp t (Pbind p x ty) b h None
  | PI_bind: forall t p x ty b h res,
    pattern_interp t p b h (Some res) ->
    pattern_interp t (Pbind p x ty) b h (Some (flet t x ty res))

with iter_pattern_interp: list term -> list pattern -> option A -> option A -> option A -> Prop :=
  | IPI_nil:
    forall b h,
    iter_pattern_interp nil nil b h b
  | IPI_cons: forall t ts p ps b h res res1,
    iter_pattern_interp ts ps b h res ->
    pattern_interp t p res h res1 ->
    iter_pattern_interp (t :: ts) (p :: ps) b h res1
  (*TODO: maybe remove these: not needed because this case is never reached.
    Only here to make the relation total*)
  | IPI_bad1: forall t ts b h,
    iter_pattern_interp (t :: ts) nil b h None
  | IPI_bad2: forall p ps b h,
    iter_pattern_interp nil (p :: ps) b h None.
Set Elimination Schemes.

Scheme pattern_interp_ind := Minimality for pattern_interp Sort Prop
with iter_pattern_interp_ind := Minimality for iter_pattern_interp Sort Prop.

(*We need another form of iteration, where failures are propagated*)
Inductive match_pattern: term -> list pattern -> list A -> option A -> Prop :=
  | MP_nil: forall t,
    match_pattern t nil nil None
  | MP_cons: forall t p ps tm ts res res1,
    match_pattern t ps ts res ->
    pattern_interp t p (Some tm) res res1 ->
    match_pattern t (p :: ps) (tm :: ts) res1.

(*Proof of equivalence*)
Lemma compile_match_interp: forall (t: term) (p: pattern) (b: option A) (h: option A) (res: option A),
  compile_match t p b h = res -> pattern_interp t p b h res.
Proof.
  intros. generalize dependent res; revert t b h; induction p; intros; simpl in *.
  - destruct b; subst; constructor.
  - destruct ps.
    + destruct (is_constr f vs t) eqn : Hcon; subst;
      constructor; rewrite Hcon; auto.
    + destruct (is_constr f vs t) eqn : Hcon.
      2 : { subst. constructor. rewrite Hcon; auto. }
      assert (forall ls ps res1, 
        Forall (fun p : pattern =>
          forall (t : term) (b h res : option A),
          compile_match t p b h = res -> pattern_interp t p b h res) ps ->
        ((fix compile_matches (tms : list term) (pats : list pattern) {struct pats} :
          option A :=
          match tms with
          | [] => match pats with
                  | [] => b
                  | _ :: _ => None
                  end
          | tm0 :: tl2 =>
              match pats with
              | [] => None
              | p1 :: tl3 =>
                  compile_match tm0 p1 (compile_matches tl2 tl3) h
              end
          end) ls ps) = res1 -> iter_pattern_interp ls ps b h res1). {
        intros ls ps'. clear H0. clear H. revert ls. induction ps'; intros.
        destruct ls; simpl in H0; subst; constructor.
        inversion H; subst.
        destruct ls as [|thd ttl]. constructor. eapply IPI_cons.
        - apply IHps'.
          auto. reflexivity.
        - apply H3. reflexivity.
      }
      specialize (H1 l (p :: ps) res); simpl in H1.
      apply H1 in H0; auto; clear H1.
      eapply PI_constrConsT.
      rewrite Hcon; reflexivity. apply H0.
  - subst; apply PI_wild.
  - eapply PI_or. apply IHp2. reflexivity. apply IHp1. assumption.
  - destruct (compile_match t p b h) eqn : Hcon; simpl in H; subst.
    + eapply PI_bind. apply IHp. assumption.
    + constructor. apply IHp. assumption.
Qed.

(*TODO: other direction*)

End PatternInterp.

(*Get term and formula versions*)

Definition compile_term_match := compile_match Tlet.
Definition compile_formula_match := compile_match Flet.

Definition term_pattern_interp := pattern_interp Tlet.
Definition formula_pattern_interp := pattern_interp Flet.

Definition match_term_pattern := match_pattern Tlet.
Definition match_formula_pattern := match_pattern Flet.

(* Function/Predicate Application *)

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
 (d: sort) (d': domain d) : domain (nth i l d).
Proof.
  generalize dependent i. induction a; simpl; intros.
  - destruct i; apply d'. 
  - destruct i.
    + simpl. apply d0.
    + apply IHa.
Defined.

Lemma arg_list_eq_ext: forall {domain: sort -> Type} {l: list sort} (a1 a2: arg_list domain l)
  (d: sort) (d': domain d),
  (forall i, i < length l -> arg_nth a1 i d d' = arg_nth a2 i d d') ->
  a1 = a2.
Proof.
  intros d l a1. dependent induction a1; simpl; intros a2; dependent induction a2;
  simpl; intros; auto. clear IHa2.
  assert (d0 = d1). {
    assert (0 < S(length tl)) by lia.
    specialize (H 0 H0). simpl in H. auto.
  }
  subst. f_equal. apply (IHa1 _ d2 d'). intros.
  assert (S(i) < S(Datatypes.length tl)) by lia.
  specialize (H _ H1). simpl in H. auto.
Qed.

(*Here, we prove that a type substitution that replaces all of the type
  parameters for a function/pred symbol with sorts results in a sort *)
Definition funsym_sigma_args (f: funsym) (s: list sort) : list sort :=
  ty_subst_list_s (s_params f) s (s_args f).

Definition funsym_sigma_ret (f: funsym) (s: list sort) : sort :=
  ty_subst_s (s_params f) s (s_ret f).

Definition predsym_sigma_args (p: predsym) (s: list sort) : list sort :=
  ty_subst_list_s (p_params p) s (p_args p).

Inductive domain_nonempty (domain: sort -> Type) (s: sort) :=
  | DE: forall (x: domain s),
    domain_nonempty domain s.

Definition dom_cast_aux (domain: sort -> Type) (v1 v2: sort) (Hv: v1 = v2) 
  (x: domain v1) : domain v2.
subst. apply x.
Defined.

Section Interp.

Variable sigma: sig.
Variable gamma: context.
Variable gamma_valid: valid_context sigma gamma. 


Lemma funsym_sigma_ret_eq: forall {c1 c2: funsym} (s: list sort) 
  (H: s_ret c1 = s_ret c2 /\ s_params c1 = s_params c2),
  funsym_sigma_ret c1 s = funsym_sigma_ret c2 s.
Proof.
  intros. unfold funsym_sigma_ret. destruct H as [Hret Hparams];
  rewrite Hret, Hparams. reflexivity.
Qed.

(*One other lemma we need for casting*)
Lemma adt_typesym_funsym: forall {a: typesym} {constrs: list funsym} {c: funsym} (s: list sort),
In (a, constrs) (datatypes_of_context gamma) ->
In c constrs ->
length (s_params c) = length s ->
funsym_sigma_ret c s = typesym_to_sort a s.
Proof.
  intros. unfold funsym_sigma_ret. unfold typesym_to_sort.
  apply sort_inj; simpl.
  pose proof (adt_constr_ret_params _ _ gamma_valid _ _ _ H H0).
  destruct H2. rewrite H2. simpl. rewrite H3. f_equal.
  apply list_eq_ext'; rewrite !map_length; rewrite <- H3; subst. lia.
  intros n d Hn.
  rewrite !(map_nth_inbound) with (d2:=d).
  2: rewrite map_length; lia.
  rewrite (map_nth_inbound) with (d2:=s_int); try lia.
  rewrite map_nth_inbound with (d2:=("x")%string); [|assumption]. 
  simpl.
  assert (NoDup (s_params c)). {
    destruct c; simpl in *. rewrite reflect_iff. apply s_params_nodup.
    apply nodup_NoDup.
  }
  assert (forall n vars (sorts : list sort) d1 d2 d3,
    length vars = length sorts ->
    NoDup vars ->
    n < length vars ->
    ty_subst_fun vars (sorts_to_tys sorts) d1 (nth n vars d2) = nth n sorts d3). {
      clear. intros n vars; revert n; induction vars; simpl; intros; [lia|].
      destruct sorts as [|s1 stl]; inversion H; simpl.
      destruct n as [|n'].
      - destruct (typevar_eq_dec a a); auto. contradiction.
      - destruct (typevar_eq_dec (nth n' vars d2) a); auto.
        + subst. inversion H0; subst.
          exfalso. apply H5. apply nth_In. lia.
        + apply IHvars; auto. inversion H0; subst; auto. lia.
  }
  apply H5; auto; try lia.
Qed.

Record pre_interp := {
  domain: sort -> Type;
  domain_int: domain s_int = Z;
  domain_real: domain s_real = R;
  domain_ne: forall s, domain_nonempty domain s;

  (*This is quite unwieldy (and could be wrong) - need to see if works/can do better*)

  funs: forall (f:funsym) (srts: list sort),
    arg_list domain (funsym_sigma_args f srts) ->
    (domain (funsym_sigma_ret f srts));

  preds: forall (p:predsym) (srts: list sort),
    arg_list domain (predsym_sigma_args p srts) -> bool;

  (*ADTs - TODO (dependent type issues)*)
  (*We don't restrict to the signature but that is OK*)
  (*TODO: dependent type issues*)
  
  adts: forall (a: typesym) (constrs: list funsym) (srts: list sort)
    (Hadt: In (a, constrs) (datatypes_of_context gamma)),
    (*1. Disjointness of constructors*)
    (*For i \neq j, [[f_i(s)]](t) \neq [[f_j(s)]](u) *)
    (forall c1 c2 (Hc1: In c1 constrs)
      (Hc2: In c2 constrs), c1 <> c2 
    (*we know constructor cannot be duplicated*) ->
      forall t u, (funs c2 srts) t <> 
        (dom_cast_aux domain _ _ 
          (funsym_sigma_ret_eq srts (adt_constr_ret_params_eq sigma _ gamma_valid Hadt Hc1 Hc2)) 
          ((funs c1 srts) u))) /\
    (*2: Injectivity of constructors *)
    (*[[f_i(s)]](t) = [f_i(s)](u) -> t = u*)
    (forall c t u, In c constrs ->
      (funs c srts) t = (funs c srts) u -> t = u) /\
    (*3: Completeness of constructors*)
    (*forall x in [[t(s)]], exists i t, x = [[f_i(s)]](t)*)
    (forall (x: domain (typesym_to_sort a srts)), 
      exists c t (Hc: In c constrs) (Hlen: length (s_params c) = length srts),
      x = (dom_cast_aux domain _ _
        (adt_typesym_funsym _ Hadt Hc Hlen) ((funs c srts) t)))
}.

(*Valuations*)
Record valuation (i: pre_interp) := {
  v_typevar : typevar -> sort;
  v_vars: forall (x: vsymbol) (v: vty), (domain i (v_subst (v_typevar) v))
}.

Section Interp.

Variable i: pre_interp.

Notation val v t  := (domain i (v_subst (v_typevar i v) t)).

Definition z_to_dom (v: valuation i) (z: Z) : val v vty_int.
Proof.
  erewrite sort_inj. rewrite (domain_int i). apply z.
  reflexivity.
Defined.

Definition r_to_dom (v: valuation i) (r: R) : val v vty_real.
Proof.
  erewrite sort_inj. rewrite (domain_real i). apply r.
  reflexivity.
Defined.

Definition var_to_dom (v: valuation i) (x: vsymbol) (t: vty) : val v t.
Proof.
  apply v_vars. apply x.
Defined. 

(*Substitution*)

(*Here, a substitution means that we replace a variable of type t
  with an element of [val t]. This affects the valuation v:
  ie: v' := v[x -> y], where y \in [[v(t)]]
  We will prove that, for all tm, [[tm]]_v' = [[tm]]_v.
  We will always be replacing variable 0 in a term (the innermost bound variable)
  *)

Definition substi (v: valuation i) (x: vsymbol) (ty: vty) (y: val v ty) : valuation i.
apply (Build_valuation i (v_typevar i v)).
intros m ty'. destruct (vsymbol_eq_dec m x).
destruct (vty_eq_dec ty ty').
- subst. apply y.
- (*trivial case*) apply (v_vars i v m ty').
- apply (v_vars i v m ty').
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

Lemma dom_cast_inj: forall (v1 v2: sort) (H: v1 = v2) (d1 d2: domain i v1),
  dom_cast v1 v2 H d1 = dom_cast v1 v2 H d2 ->
  d1 = d2.
Proof.
  intros. unfold dom_cast in H0. unfold eq_rect_r in H0.
  unfold eq_rect in H0. destruct (eq_sym H). auto.
Qed.

Definition dom_int : domain i s_int.
destruct i. simpl. rewrite domain_int0. apply 0%Z.
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
Unset Elimination Schemes.
Inductive term_interp: 
  forall (v: valuation i) (tm: term) (ty: vty) (x: domain i (v_subst (v_typevar i v) ty)), Prop :=
  | TI_int: forall v z,
    term_interp v (Tconst (ConstInt z)) vty_int (z_to_dom v z)
  | TI_real: forall v r,
    term_interp v (Tconst (ConstReal r)) vty_real (r_to_dom v r)
  | TI_var: forall v (x: vsymbol) (ty: vty),
    term_interp v (Tvar x ty) ty (var_to_dom v x ty)
  | TI_iftrue: forall v f t1 t2 ty x tl fl,
    formula_interp v tl fl f true ->
    term_interp v t1 ty x ->
    term_interp v (Tif f t1 t2) ty x
  | TI_iffalse: forall v f t1 t2 ty x tl fl,
    formula_interp v tl fl f false ->
    term_interp v t2 ty x ->
    term_interp v (Tif f t1 t2) ty x
  (*substitution changes the valuation *)
  | TI_let: forall v t1 (x: vsymbol) t2 ty1 ty2 x1 x2,
    term_interp v t1 ty1 x1 ->
    term_interp (substi v x ty1 x1) t2 ty2 x2 ->
    term_interp v (Tlet t1 x ty1 t2) ty2 x2
  | TI_func: forall (v: valuation i) (f: funsym) (params: list vty) (ts: list term) 
    (Hlen: length (s_params f) = length params) xs,

    let v_map := v_subst (v_typevar i v) in
    (* First, we get the interpretation of f *)
    let f_interp := (funs i) f (map v_map params)  in
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
      term_interp v (nth n ts (Tconst (ConstInt 0)))
        (nth n f_arg_typs s_int) 
        (dom_cast _ _ (subst_sort_eq (nth n f_arg_typs s_int) (v_typevar i v)) 
          (@arg_nth _ f_arg_typs xs n s_int dom_int))) ->
    
    (*Again, we must cast the return type of f, for the same reason*)
    term_interp v (Tfun f params ts) f_ret 
      (dom_cast _ _ (subst_sort_eq f_ret (v_typevar i v)) (f_interp xs))

with formula_interp: (valuation i) -> list formula -> list formula -> formula -> bool -> Prop :=
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
  | FI_let: forall v t (x: vsymbol) ty f x1 b tl fl,
    term_interp v t ty x1 ->
    formula_interp (substi v x ty x1) tl fl f b ->
    formula_interp v tl fl (Flet t x ty f) b
  | FI_forallT: forall v x ty f tl fl,
    (forall d, formula_interp (substi v x ty d) tl fl f true) ->
    formula_interp v tl fl (Fquant Tforall x ty f) true
  (*TODO: may not need this with classical part*)
  | FI_forallF: forall v x ty f d tl fl, (*otherwise we cannot prove that forall is false*)
    (formula_interp (substi v x ty d) tl fl f false) ->
    formula_interp v tl fl (Fquant Tforall x ty f) false
  | FI_existsT: forall v x ty f d tl fl,
    (formula_interp (substi v x ty d) tl fl f true) ->
    formula_interp v tl fl (Fquant Texists x ty f) true
  | FI_existsF: forall v x ty f tl fl,
    (forall d, formula_interp (substi v x ty d) tl fl f false) ->
    formula_interp v tl fl (Fquant Texists x ty f) false
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
  | FI_prop: forall (v: valuation i) (p: predsym) (params: list vty) (ts: list term) 
    (Hlen: length (p_params p) = length params) xs tl fl,

    (*Very similar to function*)

    let v_map := v_subst (v_typevar i v) in
    (* First, we get the interpretation of p *)
    let p_interp := (preds i) p (map v_map params)  in
    (*let f_ret := (funsym_sigma_ret f (map v_map params) 
      (map_length_eq v_map _ _ Hlen)) in*)

    (*The list of sigma(s_args)_i*)
    let p_arg_typs : list sort :=
      predsym_sigma_args p (map v_map params) in
    (*ith elt of xs is [[t_i]]_v. We need to cast the types to get the type as
      [[v(sigma(s_args f)_i)]]*)

    (forall n (Hn: n < length p_arg_typs),
      term_interp v (nth n ts (Tconst (ConstInt 0)))
        (nth n p_arg_typs s_int) 
        (dom_cast _ _ (subst_sort_eq (nth n p_arg_typs s_int) (v_typevar i v)) 
          (@arg_nth _ p_arg_typs xs n s_int dom_int))) ->

    formula_interp v tl fl (Fpred p params ts) (p_interp xs)
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
    formula_interp v tl fl f false.
(*TODO: do we need some weakening rules/ways to manipulate the context?
  For example:
    formula_interp v tl fl f true ->
    formula_interp v (t :: tl) fl f true
  Also, if we have a derivation, and know that some formula is "in" the
  list of assumptions, how do we use this info?
  I'm not sure this definition is super usable/complete at the moment*)
Set Elimination Schemes.

Scheme term_interp_ind := Minimality for term_interp Sort Prop
with formula_interp_ind := Minimality for formula_interp Sort Prop.

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

Section Ex.

Local Open Scope string_scope.
(*Let's give an example: prove that equality is reflexive*)
Lemma prove_eq_refl: forall (v: valuation i) (a: vty) tl fl,
  formula_interp v tl fl (Fquant Tforall "x" a (Feq a (Tvar "x" a) (Tvar "x" a))) true.
Proof.
  intros v a. constructor. intros d.
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
Definition triv_val (i: pre_interp) : valuation i.
apply (Build_valuation i (fun _ => s_int)).
intros.
destruct i; simpl. specialize (domain_ne0 (v_subst (fun _ : typevar => s_int) v)).
inversion domain_ne0. apply x0.
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
Fixpoint mk_fun_arg {A: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (i: pre_interp) v_var
  (l: list A) (s: list sort) (a: arg_list (domain i) s) (x: A): 
    forall v, domain i (v_subst v_var v) :=
  match l, a with
  | hd :: tl, AL_cons _ shd stl d t => 
    fun v =>
      (*Need to know that types are equal so we can cast the domain*)
      match (vty_eq_dec (v_subst v_var v)) shd with
      | left Heq => if eq_dec hd x then dom_cast _ _ _ (sort_inj _ _ (eq_sym Heq)) d
          else mk_fun_arg eq_dec i v_var tl stl t x v
      | _ => mk_fun_arg eq_dec i v_var tl stl t x v
      end
  (* Otherwise, return default element of domain *)
  | _, _ => fun v => match domain_ne i (v_subst v_var v) with
                      | DE _ _ y => y
                      end
  end.

(*Build valuation from a list, ie: the valuation that sends each element of vs
  to the corresponding sort in s and each element of syms to the
  corresponding element of a (modulo dependent type stuff)
  Give default values if something is not in the list*)
Definition make_val (i: pre_interp) (vs: list typevar) (s1 s2: list sort)
  (syms: list vsymbol) (a: arg_list (domain i) s2) : valuation i :=
  let v_var := (ty_subst_fun_s vs s1 s_int) in
  Build_valuation i v_var
    (mk_fun_arg vsymbol_eq_dec i v_var syms s2 a).

(* Interpretation, Satisfiability, Validity *)

Section Logic.


(*A full interpretation is consistent with recursive and inductive definitions*)
Definition full_interp (p: pre_interp) : Prop :=
  (*For each function f(alpha)(x) = t, 
    [[f(s)]](y) = [[t]]_v, where v maps alpha -> s and x -> y*)
  (*Note that y_i has type [[sigma(tau_i)]], where sigma maps alpha -> s*)
  (forall (f: funsym) (vs: list vsymbol) (t: term) (s: list sort) 
    (Hs: length (s_params f) = length s),
    In (f, vs, t) (fundefs_of_context gamma) ->
   
    forall ts,
    let v := make_val p (s_params f) s (funsym_sigma_args f s) vs ts in
      term_interp p v t (s_ret f) ((funs p) f s ts)) /\
  (*For each predicate p(alpha)(x) = f, 
    [[p(s)]](y) = [[f]]_v, where v maps alpha -> s and x -> y*)
  (forall (pd: predsym) (vs: list vsymbol) (f: formula) (s: list sort)
    (Hs: length (p_params pd) = length s),
    In (pd, vs, f) (preddefs_of_context gamma) ->
    
    (*TODO: all lists or nil ones?*)
    forall ts l1 l2,
    let v := make_val p (p_params pd) s (predsym_sigma_args pd s) vs ts in
      formula_interp p v l1 l2 f ((preds p) pd s ts)
  ).
  (*TODO: inductive predicates*)

Definition closed (f: formula) : Prop := closed_formula f /\ valid_formula sigma f.

Definition interp : Type := {i: pre_interp | full_interp i}.

Coercion get_pre_interp (i: interp) : pre_interp := proj1_sig i.

(*TODO: is this all lists of assumptions/antiassumptions - or nil ones?*)
Definition satisfied_f (i: interp) (f: formula) : Prop :=
  closed f /\ forall v, formula_interp i v nil nil f true.

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

End Interp.