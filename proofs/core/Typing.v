Require Export Vars.
Set Bullet Behavior "Strict Subproofs".

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
    (forall x, In x (combine ps (map sigma (s_args f))) ->
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
Inductive term_has_type: sig -> term -> vty -> Prop :=
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
    (*let sigma : vty -> vty := ty_subst (s_params f) params in*)
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
    (*we defer the check for algebraic datatypes or exhaustiveness until
      later, because we need an additional context*)
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
    let sigma : vty -> vty := ty_subst (s_params p) params in
    Forall (fun x => term_has_type s (fst x) (snd x))
      (combine tms (map sigma (s_args p))) ->
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
    term_has_type s tm ty ->
    Forall(fun x => pattern_has_type s (fst x) ty) ps ->
    Forall (fun x => valid_formula s (snd x)) ps ->
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
    ) ((f_ret f) :: (s_args f))
  ) (sig_f s) /\
  (*Predicate symbols are quite similar*)
  Forall (fun (p: predsym) =>
    Forall (fun (t: vty) => 
      valid_type s t /\ Forall (fun (fv: typevar) => In fv (s_params p)) (type_vars t)
    ) (s_args p)
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

Definition mutfuns_of_context (c: context) : list (list funpred_def) :=
  fold_right (fun o acc =>
    match o with
    | recursive_def lf => lf :: acc
    | _ => acc
    end) nil c.

(*Definition fundefs_of_context (c: context) : list (funsym * list vsymbol * term) :=
  concat (map fundefs_of_def c).

Definition preddefs_of_context (c: context) : list (predsym * list vsymbol * formula) :=
  concat (map preddefs_of_def c).*)

Definition indpreds_of_context (c: context) : list (predsym * list formula) :=
  concat (map indpreds_of_def c).

Definition typesyms_of_context (c: context) : list typesym :=
  map fst (datatypes_of_context c).

Definition funsyms_of_context (c: context) : list funsym :=
  concat (map funsyms_of_def c).

Definition predsyms_of_context (c: context) : list predsym :=
  concat (map predsyms_of_def c).

(*Ways of dealing with adts and parts in context*)
(*We want booleans for proof irrelevance*)

(*TODO: dont duplicate*)
Ltac right_dec := 
  solve[let C := fresh "C" in right; intro C; inversion C; try contradiction].

Definition adt_dec: forall (x1 x2: alg_datatype), {x1 = x2} + {x1 <> x2}.
intros [t1 c1] [t2 c2].
destruct (typesym_eq_dec t1 t2); [|right_dec].
destruct (ne_list_eq_dec funsym_eq_dec c1 c2); [|right_dec].
left. rewrite e, e0; reflexivity.
Defined.

Definition mut_adt_dec: forall (m1 m2: mut_adt), {m1 = m2} + {m1 <> m2}.
intros m1 m2. destruct m1, m2.
destruct (list_eq_dec adt_dec typs typs0); subst; [|right_dec].
destruct (list_eq_dec typevar_eq_dec m_params m_params0); subst;[|right_dec].
left. f_equal. apply bool_irrelevance.
Defined.

(*Utilities for dealing with mutual types and context*)
Section MutADTUtil.

Definition mut_in_ctx (m: mut_adt) (gamma: context) :=
  in_bool mut_adt_dec m (mut_of_context gamma).

Lemma mut_in_ctx_eq: forall m gamma,
  mut_in_ctx m gamma <-> In m (mut_of_context gamma).
Proof.
  intros. symmetry. 
  apply (reflect_iff _ _ (in_bool_spec mut_adt_dec m (mut_of_context gamma))).
Qed.

Lemma mut_in_ctx_eq2: forall m gamma,
  mut_in_ctx m gamma <-> In (datatype_def m) gamma.
Proof.
  intros. rewrite mut_in_ctx_eq. symmetry.
  unfold mut_of_context, mut_in_ctx.
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

(*For recursive functions, it is VERY helpful for this to be
  a (proof irrelevant) boolean*)
Definition adt_in_mut (a: alg_datatype) (m: mut_adt) :=
  in_bool adt_dec a (typs m).

Definition ts_in_mut_list (ts: typesym) (m: list alg_datatype) : bool :=
  in_bool typesym_eq_dec ts (map adt_name m).


Lemma ts_in_mut_list_ex: forall ts m,
  ts_in_mut_list ts (typs m) -> { a | ts = adt_name a /\ 
  adt_in_mut a m}.
Proof.
  unfold adt_in_mut, ts_in_mut_list; intros. induction (typs m); simpl.
  - simpl in H. inversion H.
  - simpl in H.
    destruct (typesym_eq_dec ts (adt_name a)); subst.
    + apply (exist _ a). rewrite eq_dec_refl. split; auto.
    + specialize (IHl H).
      destruct IHl as [a' [Ha' Hina']].
      apply (exist _ a'). rewrite Hina'. subst; simpl_bool; split; auto.
Qed.

Lemma ts_in_mut_list_spec: forall ts m,
  ts_in_mut_list ts (typs m) <-> exists a, ts = adt_name a /\ 
  adt_in_mut a m.
Proof.
  intros. unfold adt_in_mut, ts_in_mut_list. induction (typs m); simpl.
  - split; intros; auto. inversion H. destruct H as [a [H]]; inversion H0.
  - split; intros.
    + destruct (typesym_eq_dec ts (adt_name a)).
      * subst. exists a. rewrite eq_dec_refl. split; auto.
      * apply IHl in H. destruct H as [a' [Ha' Hina']].
        subst. exists a'. rewrite Hina'. simpl_bool. split; auto.
    + destruct H as [a' [Ha' Hina']]; subst.
      destruct (adt_dec a' a); subst; simpl in Hina'.
      * rewrite eq_dec_refl. reflexivity.
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

(*Now we need utilities for finding the ADT/mutual adt that a
  type belongs to*)

(*For pattern matches (and for typing info), 
  we need to look at an element of type s, 
  determine if s is an ADT type, and if so,
  extract the components (constructor and args). We need
  a lot of machinery to do this; we do this here.*)

Definition find_ts_in_mut (ts: typesym) (m: mut_adt) : option alg_datatype :=
  find (fun a => typesym_eq_dec ts (adt_name a)) (typs m).

Lemma find_ts_in_mut_none: forall ts m,
  find_ts_in_mut ts m = None <->
  forall a, adt_in_mut a m -> adt_name a <> ts.
Proof.
  intros. unfold find_ts_in_mut.
  rewrite find_none_iff.
  split; intros Hall x Hin.
  - intro C; subst.
    apply in_bool_In in Hin.
    specialize (Hall _ Hin). simpl_sumbool. contradiction.
  - apply (In_in_bool adt_dec) in Hin.
    specialize (Hall _ Hin).
    destruct (typesym_eq_dec ts (adt_name x)); auto; subst;
    contradiction.
Qed.

Lemma find_ts_in_mut_some: forall ts m a,
  find_ts_in_mut ts m = Some a ->
  adt_in_mut a m /\ adt_name a = ts.
Proof.
  intros ts m a Hf. apply find_some in Hf.
  destruct Hf as [Hin Heq].
  split; auto. apply In_in_bool; auto.
  simpl_sumbool.
Qed.

Lemma find_ts_in_mut_iff: forall ts m a,
  NoDup (map adt_name (typs m)) ->
  (find_ts_in_mut ts m = Some a) <-> (adt_in_mut a m /\ adt_name a = ts).
Proof.
  intros. eapply iff_trans. apply find_some_nodup.
  - intros. repeat simpl_sumbool.
    apply (NoDup_map_in H); auto.
  - simpl. unfold adt_in_mut. split; intros [Hin Hname];
    repeat simpl_sumbool; split; auto; try simpl_sumbool;
    apply (reflect_iff _ _ (in_bool_spec adt_dec a (typs m))); auto.
Qed.

Definition vty_in_m (m: mut_adt) (vs: list vty) (v: vty) : bool :=
  match v with
  | vty_cons ts vs' => 
    ssrbool.isSome (find_ts_in_mut ts m) &&
    list_eq_dec vty_eq_dec vs' vs
  | _ => false
  end.

Definition vty_m_adt (m: mut_adt) (vs: list vty) (v: vty) : option (alg_datatype) :=
  match v with
  | vty_cons ts vs' =>
      if list_eq_dec vty_eq_dec vs' vs then
         find_ts_in_mut ts m
      else None
  | _ => None
  end.

Lemma vty_in_m_spec (m: mut_adt) (vs: list vty) (v: vty):
  reflect 
  (exists a, adt_in_mut a m /\ v = vty_cons (adt_name a) vs)
  (vty_in_m m vs v) .
Proof.
  unfold vty_in_m. destruct v; try solve[apply ReflectF; intros [a [Ha Heq]]; inversion Heq].
  destruct (find_ts_in_mut t m) eqn : Hfind; simpl.
  - apply find_ts_in_mut_some in Hfind.
    destruct Hfind; subst.
    destruct (list_eq_dec vty_eq_dec l vs); subst; simpl.
    + apply ReflectT. exists a. split; auto.
    + apply ReflectF. intros [a' [Ha' Heq]]; inversion Heq; subst;
      contradiction.
  - apply ReflectF. rewrite find_ts_in_mut_none in Hfind.
    intros [a [Ha Heq]]; subst.
    inversion Heq; subst.
    apply (Hfind a Ha); auto.
Qed. 

Definition vsym_in_m (m: mut_adt) (vs: list vty) (x: vsymbol) : bool :=
  vty_in_m m vs (snd x).


(*From a list of vsymbols, keep those which have type vty_cons a ts
  for some a in mut_adt m*)
Definition vsyms_in_m (m: mut_adt) (vs: list vty) (l: list vsymbol) :
  list vsymbol :=
  filter (vsym_in_m m vs) l.

(*A more useful formulation*)
Lemma vsyms_in_m_in (m: mut_adt) (vs: list vty) (l: list vsymbol):
  forall x, In x (vsyms_in_m m vs l) <-> In x l /\ exists a,
    adt_in_mut a m /\ snd x = vty_cons (adt_name a) vs.
Proof.
  intros. unfold vsyms_in_m, vsym_in_m, vty_in_m.
  rewrite in_filter. rewrite and_comm. bool_to_prop.
  destruct x; simpl in *. destruct v; try (solve[split; [intro C; inversion C | 
    intros [a [a_in Hty]]; inversion Hty]]).
  unfold ssrbool.isSome.
  destruct (find_ts_in_mut t m) eqn : Hts; simpl.
  - destruct (list_eq_dec vty_eq_dec l0 vs); subst; simpl; split;
    intros; auto; try tf.
    + exists a. apply find_ts_in_mut_some in Hts. destruct Hts.
      subst. split; auto.
    + destruct H as [a' [Ha' Hty]]. inversion Hty; subst; auto.
  - split; [intro C; inversion C | intros [a [Ha Hty]]].
    rewrite find_ts_in_mut_none in Hts.
    inversion Hty; subst.
    apply Hts in Ha. contradiction.
Qed.

Definition constr_in_m (f: funsym) (m: mut_adt) : bool :=
  existsb (fun a => constr_in_adt f a) (typs m).

End MutADTUtil.


(*We also require that all type variables in mutually recursive types
  are correct: all component types and constructors have the same
  parameters*)
Definition valid_mut_rec (m: mut_adt) : Prop :=
  Forall (fun a => (m_params m) = (ts_args (adt_name a)) /\
    Forall (fun (f: funsym) => (m_params m) = (s_params f)) 
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

(*TODO: move this maybe*)

(* Additional checks for pattern matches *)

(*In addition to what we have above, we also need to know that pattern
  matches operate on an algebraic data type and are exhaustive. We separate this
  check from the main typing relation for 2 reasons:
  1. The exhaustiveness check relies on well-typedness in a non-strictly-positive way
  2. This check depends on the context, as opposed to the typing relation, which only
    depends on the signature. *) 

(*TODO: this does NOT work for exhaustiveness checking,
  since we can never prove it, we do need to check
  that the pattern match occurs on an ADT 
*)

Section MatchExhaustive.

Variable sigma: sig.
Variable gamma: context.

(*
(*Describes when a pattern matches a term*)
Inductive matches : pattern -> term -> Prop :=
  | M_Var: forall v t,
    matches (Pvar v) t
  | M_Constr: forall (m: mut_adt) (a: alg_datatype) 
      (f: funsym) (vs: list vty) (ps: list pattern) (ts: list term),
    mut_in_ctx m gamma ->
    adt_in_mut a m ->
    constr_in_adt f a ->
    (forall x, In x (combine ps ts) -> matches (fst x) (snd x)) ->
    matches (Pconstr f vs ps) (Tfun f vs ts)
  | M_Wild: forall t,
    matches Pwild t
  | M_Or: forall p1 p2 t,
    matches p1 t \/ matches p2 t ->
    matches (Por p1 p2) t
  | M_Bind: forall p x t,
    matches p t ->
    matches (Pbind p x) t.

(*A match is exhaustive if for every instance of an alg_datatype,
  some pattern matches it*)
Definition exhaustive_match (a: alg_datatype) (args: list vty)
  (ps: list pattern) : Prop :=
  adt_in_ctx a gamma /\
  forall t, term_has_type sigma t (vty_cons (adt_name a) args) ->
    exists p, In p ps /\ matches p t.*)


(*For now, we say that a valid pattern match is one that matches
  on an ADT*)
Fixpoint All {A: Type} (P: A -> Prop) (l: list A) {struct l} : Prop :=
  match l with
  | nil => True
  | x :: xs => P x /\ All P xs
  end.
Definition iter_and (l: list Prop) : Prop :=
  fold_right and True l.

(*TODO: need to require somewhere that pattern constructors
  have to actually be constructors*)
Fixpoint valid_matches_tm (t: term) : Prop :=
  match t with
  | Tfun f vs tms => iter_and (map valid_matches_tm tms)
  | Tlet tm1 v tm2 => valid_matches_tm tm1 /\ valid_matches_tm tm2
  | Tif f1 t1 t2 => valid_matches_fmla f1 /\ valid_matches_tm t1 /\
    valid_matches_tm t2
  | Tmatch tm v ps =>
    valid_matches_tm tm /\
    (*the type v is an ADT applied to some valid arguments
      (validity from typing)*)
    (exists a m args, mut_in_ctx m gamma /\
      adt_in_mut a m /\
      v = vty_cons (adt_name a) args) /\
    iter_and (map (fun x => valid_matches_tm (snd x)) ps)
      (*iter_and (map valid_matches_tm (map snd ps))*)
  | Teps f x => valid_matches_fmla f
  | _ => True
  end
with valid_matches_fmla (f: formula) : Prop :=
  match f with
  | Fpred p vs tms => iter_and (map valid_matches_tm tms)
  | Fquant q v f => valid_matches_fmla f
  | Feq v t1 t2 => valid_matches_tm t1 /\ valid_matches_tm t2
  | Fbinop b f1 f2 => valid_matches_fmla f1 /\
    valid_matches_fmla f2
  | Fnot f => valid_matches_fmla f
  | Flet t v f => valid_matches_tm t /\ valid_matches_fmla f
  | Fif f1 f2 f3 => valid_matches_fmla f1 /\
    valid_matches_fmla f2 /\ valid_matches_fmla f3
  | Fmatch t v ps =>
    valid_matches_tm t /\
    (*the type v is an ADT applied to some valid arguments
      (validity from typing)*)
    (exists a m args, mut_in_ctx m gamma /\
      adt_in_mut a m /\
      v = vty_cons (adt_name a) args) /\
    iter_and (map (fun x => valid_matches_fmla (snd x)) ps)
  | _ => True
  end.

End MatchExhaustive.

(*The full typing judgement for terms and formulas*)
Definition well_typed_term (s: sig) (gamma: context) (t: term) (ty: vty) : Prop :=
  term_has_type s t ty /\ valid_matches_tm gamma t.

Definition well_typed_formula (s: sig) (gamma: context) (f: formula) : Prop :=
  valid_formula s f /\ valid_matches_fmla gamma f.

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
      (f_ret c) = vty_cons ts (map vty_var (ts_args ts))) 
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

(* Recursive Functions and Predicates *)
Section FunPredSym.

Variable s: sig.
Variable gamma: context.

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
  sn_idx: nat; (*sn_idx_in: sn_idx <? length sn_args;*)
  (*sn_args_len: length sn_args =? length (s_args sn_sym);
  sn_args_nodup: nodupb vsymbol_eq_dec sn_args*)}.

Definition sn_wf (s: sn): Prop :=
  sn_idx s < length (sn_args s) /\
  length (sn_args s) = length (s_args (sn_sym s)) /\
  NoDup (sn_args s) /\
  map snd (sn_args s) = s_args (sn_sym s).

Record fn := mk_fn {fn_sym: funsym; fn_sn : sn;
  fn_body: term; (*fn_wf: f_sym fn_sym = sn_sym fn_sn*)}.

Coercion fn_sn : fn >-> sn.

Definition fn_wf (f: fn) : Prop :=
  sn_wf f /\
  f_sym (fn_sym f) = sn_sym (fn_sn f).

Record pn := mk_pn {pn_sym: predsym; pn_sn: sn;
  pn_body: formula; (*pn_wf: p_sym pn_sym = sn_sym pn_sn*)}.

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



(*Decidable equality*)
(*
Lemma sn_eq (s1 s2: sn) :
  sn_sym s1 = sn_sym s2 ->
  sn_args s1 = sn_args s2 ->
  sn_idx s1 = sn_idx s2 ->


Definition sn_eqb  (s1 s2: sn) : bool :=
  fpsym_eqb (sn_sym s1) (sn_sym s2) &&
  list_eqb vsymbol_eqb (sn_args s1) (sn_args s2) &&
  (sn_idx s1 =? sn_idx s2).*)


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

(*Definition fundef_to_fn (f: funsym) (vars: list vsymbol) (t: term)
  (i: nat) (Hi: i < length (s_args f)) (Hn: NoDup vars) 
  (Hlen: length vars = length (s_args f)) : fn :=
  mk_fn f (mk_sn (f_sym f) vars i 
    (ssrbool.introT (Nat.ltb_spec0 _ _) 
      (eq_ind _ (fun x => i < x) Hi _ (eq_sym Hlen)))
    (ssrbool.introT (Nat.eqb_spec _ _) Hlen) 
    (ssrbool.introT (nodup_NoDup _ _) Hn)) t eq_refl.*)

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

(*Definition preddef_to_pn (p: predsym) (vars: list vsymbol) (f: formula)
(i: nat) (Hi: i < length (s_args p)) (Hn: NoDup vars) 
(Hlen: length vars = length (s_args p)) : pn :=
mk_pn p (mk_sn (p_sym p) vars i 
  (ssrbool.introT (Nat.ltb_spec0 _ _) 
    (eq_ind _ (fun x => i < x) Hi _ (eq_sym Hlen)))
  (ssrbool.introT (Nat.eqb_spec _ _) Hlen) 
  (ssrbool.introT (nodup_NoDup _ _) Hn)) f eq_refl.*)

Definition funpred_sym (fd: funpred_def) : fpsym :=
  match fd with
  | fun_def f _ _ => f
  | pred_def p _ _ => p
  end.

Definition funpred_args (fd: funpred_def) : list vsymbol :=
  match fd with
  | fun_def _ a _ => a
  | pred_def _ a _ => a
  end.

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
(*TODO: handle type vars? Do we need to, or is that handled by wf of f?*)
(*TODO: prove that it is handled by the typing of t/f, or enforce
  all typevars in term must appear in params*)
Definition funpred_def_valid_type (fd: funpred_def) : Prop :=
  match fd with
  | fun_def f vars t =>
    well_typed_term s gamma t (f_ret f) /\
    sublist (tm_fv t) vars /\
    sublist (tm_type_vars t) (s_params f) /\
    NoDup (map fst vars) /\
    map snd vars = s_args f (*types of args correct*)
  | pred_def p vars f =>
    well_typed_formula s gamma f /\
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

Definition separate_either {A B: Set} (l: list (Either A B)) :
  list A * list B :=
  fold_right (fun x acc =>
    let tl := acc in
    match x with
    | Left y => (y :: fst tl, snd tl)
    | Right y => (fst tl, y :: snd tl)
    end) (nil, nil) l.

Lemma separate_either_length {A B: Set} (l: list (Either A B)):
  length (fst (separate_either l)) + length (snd (separate_either l)) =
  length l.
Proof.
  induction l; simpl; auto; destruct a; simpl; lia.
Qed.

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



(*Definition sort_funpred_defs (l: list funpred_def) :
list funpred_def :=
  let t := split_funpred_defs l in
  (map (fun x => fun_def (fst (fst x)) (fst (snd x)) (snd x))).
  filter (fun x => match x with | fun_def _ _ _ => true | pred_def _ _ _ => false end) l
  ++
  filter (fun x => match x with | fun_def _ _ _ => false | pred_def _ _ _ => true end) l.

Lemma sort_funpred_defs_in: forall l f,
  In f (sort_funpred_defs l) <-> In f l.
Proof.
  intros. unfold sort_funpred_defs. rewrite in_app_iff.
  destruct f; rewrite !in_filter; split; intros; destruct_all; auto.
Qed.

Lemma sort_funpred_defs_len: forall l,
  length (sort_funpred_defs l) = length l.
Proof.
  induction l; simpl; auto.
  unfold sort_funpred_defs in *; simpl; destruct a; simpl;
  rewrite !app_length in *; simpl; lia.
Qed. *)

(*First, create list of fs and ps - do with tactics for now*)
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
(*
Require Import Coq.Sorting.Permutation.


Lemma split_funpred_defs_perm (l: list funpred_def):
  Permutation (map (fun x => f_sym (fst (fst x))) (fst (split_funpred_defs l)) ++
  map (fun x => p_sym (fst (fst x))) (snd (split_funpred_defs l)))
  (map funpred_sym l).
Proof.
  induction l as [| h t IH]; simpl; auto.
  destruct h; simpl.
  - apply Permutation_cons; auto.
  - eapply Permutation_trans. apply Permutation_sym.
    apply Permutation_middle. apply Permutation_cons; auto.
Qed.*)

Lemma map_fst_fst_fst_combine: forall {A B C D: Type} l1 l2,
  length l1 = length l2 ->
  map (fun (x : A * B * C * D) => fst (fst (fst x)))
    (combine l1 l2) =
  map (fun (x: A * B * C) => fst (fst x)) l1. 
  intros. generalize dependent l2. induction l1; simpl; intros; auto;
  destruct l2; simpl; auto; inversion H. rewrite IHl1; auto.
Qed.

(*Alt - produce the list*)


(*We want the ith element of (map snd l) to be the ith sn_idx.
  So we first create the fn and pn's, then separate them*)
  (*
let t := separate_either(
map (fun x =>
  match x with
  | fun_def f vs t => Left _ _ (f, vs, t)
  | pred_def p vs f => Right _ _ (p, vs, f)
  end) l) in
((map (fun (x: (funsym * list vsymbol * term) * nat) =>
  fundef_to_fn (fst (fst (fst x)))
    (snd (fst (fst x))) (snd (fst x)) (snd x)
  )) (combine (fst t) li1),
(map (fun (x: (predsym * list vsymbol * formula) * nat) =>
  preddef_to_pn (fst (fst (fst x)))
    (snd (fst (fst x))) (snd (fst x)) (snd x)
  )) (combine (snd t) li2)).*)


(*Lemma funpred_defs_to_sns_length: forall l li,
  length (fst (funpred_defs_to_sns l li)) +
  length (snd (funpred_defs_to_sns l li)) =
  length l.
Proof.
  intros. unfold funpred_defs_to_sns. 
  rewrite separate_either_length, map_length.
  reflexivity.
Qed.*)

Definition sn_d : sn :=
  (mk_sn id_sym [vs_d] 0).

  (*NOTE: this is not true, we just add an i when we get one
    We need the list to be ordered already for this to be
    the case*)
(*TODO*)
(*
Lemma funpred_defs_to_sns_idx: forall l i,
  i < length l ->
  sn_idx (nth i (map fn_sn (fst (funpred_defs_to_sns l)) ++
    map pn_sn (snd (funpred_defs_to_sns l))) sn_d) =
  nth i (map snd l) 0.
Proof.
  unfold funpred_defs_to_sns.
  induction l as [| h t]; simpl; intros. lia. simpl.
  destruct h as [shd ihd]. simpl. destruct shd; simpl; destruct i; simpl; auto.
  - apply IHt. lia.
  - destruct (fst (funpred_defs_to_sns t)) eqn : Hfs; simpl; auto.
    specialize (IHt 0). destruct t. simpl in H.
    simpl in IHt.
    lia.

  
  simpl.
  ->
  *)

Fixpoint filterMap {A B: Type} (f: A -> bool) (g: {x: A | f x} -> B) (l: list A):
  list B :=
  match l with
  | nil => nil
  | x :: t =>
    match f x as b return f x = b -> list B with
    | true => fun Hfa => (g (exist _ _ Hfa)) :: filterMap f g t
    | false => fun _ => filterMap f g t
    end eq_refl
  end.

(*Print split_funpred_defs.
Lemma split_funpred_defs_filter l:
  split_funpred_defs l =
  fold_right (fun x => match x wit)

  (map (fun x =>
    match ))*)

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

(*What about this?*)
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


(*TODO: do without dependent, then prove wf with assumptions*)
(*TODO: require {is: list nat | P is}
  so we can use directly - then prove typechecker, maybe later
  (after decrease_fun and decrease_pred complete*)
(*
Definition funpred_defs_to_sns (l: list funpred_def) (is: list nat)
(Hlen: length is = length l)
(Hall: forall i, i < length is -> 
  nth i is 0 < length (s_args (funpred_sym (nth i l fd_d))))
(Hl: Forall funpred_def_valid_type l) : 
  (list fn * list pn).
Proof.
  generalize dependent l. induction is; simpl; intros.
  - destruct l.
    + exact (nil, nil).
    + exact (False_rect _ (Nat.neq_0_succ (length l) Hlen)).
  - destruct l.
    + exact (False_rect _ (Nat.neq_succ_0 (length is) Hlen)).
    + simpl in Hlen. injection Hlen; intros. 
      specialize (IHis _ H (fun i Hi => Hall (S i) (Arith_prebase.lt_n_S_stt _ _ Hi)) (Forall_inv_tail Hl)).
      (*Now we need to see which one to add to*)
      destruct f.
      * exact ((fundef_to_fn f l0 t a 
          (Hall 0 (Nat.lt_0_succ (length is))) 
          (NoDup_map_inv _ _ (proj1 (proj2 (proj2 (proj2 (Forall_inv Hl)))))) 
          (proj1 (proj2 (proj2 (Forall_inv Hl))))) :: fst IHis, snd IHis).
      * exact (fst IHis, (preddef_to_pn p l0 f a 
          (Hall 0 (Nat.lt_0_succ (length is))) 
          (NoDup_map_inv _ _ (proj1 (proj2 (proj2 (proj2 (Forall_inv Hl)))))) 
          (proj1 (proj2 (proj2 (Forall_inv Hl))))) :: snd IHis).
Defined.*)

(*TODO: name (term is termination)*)
(*It is crucial that this is a sigma type, NOT "exists",
  because in our function, we actually need to know
  which arguments terminate*)
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
    (*TODO: see if we can prove the params/typesyms part*)
    Forall (fun (f: fn) => decrease_fun fs ps nil 
      (Some (nth (sn_idx f) (sn_args f) vs_d)) m vs (fn_body f)) fs /\
    Forall (fun (p: pn) => decrease_pred fs ps nil 
      (Some (nth (sn_idx p) (sn_args p) vs_d)) m vs (pn_body p)) ps.

Definition funpred_def_term_exists (l: list funpred_def) :=
  exists (m: mut_adt) (params: list typevar) (vs: list vty)
  (is: list nat),
  funpred_def_term l m params vs is.

 (* ive our termination condition*)
(*
Definition funpred_def_term (l: list funpred_def)
  (Hl: Forall funpred_def_valid_type l) : Prop :=
  exists 
  (m: mut_adt)
  (params: list typevar)
  (vs: list vty)
  (Hvs: length vs = length (m_params m))
  (m_in: mut_in_ctx m gamma)
  (is: list nat)
  (Hlen: length is = length l)
  (Hall: forall i, i < length is -> 
    nth i is 0 < length (s_args (funpred_sym (nth i l fd_d)))),
  let fs := fst (funpred_defs_to_sns l is Hlen Hall Hl) in
  let ps := snd (funpred_defs_to_sns l is Hlen Hall Hl) in
  (*All functions recurse on ADT instance*)
  (forall f, In f fs -> 
    vty_in_m m vs (snd (nth (sn_idx f) (sn_args f) vs_d))) /\
  (forall p, In p ps ->
    vty_in_m m vs (snd (nth (sn_idx p) (sn_args p) vs_d))) /\
  (*All functions have params = params*)
  (forall f, In f fs -> s_params (fn_sym f) = params) /\
  (forall p, In p ps -> s_params (pn_sym p) = params) /\
  (*TODO: see if we can prove the params part*)
  (*All functions are structurally (mutually) decreasing
    on mut type m(vs)*)
  Forall (fun (f: fn) => decrease_fun fs ps nil 
    (Some (nth (sn_idx f) (sn_args f) vs_d)) m vs (fn_body f)) fs /\
  Forall (fun (p: pn) => decrease_pred fs ps nil 
    (Some (nth (sn_idx p) (sn_args p) vs_d)) m vs (pn_body p)) ps.
*)
(*Now, the final requirement for a well-typed mutually
  recursive function definition: combine these*)

(*Note: this is NOT a Prop like the others - is this a problem?*)
Definition funpred_valid_type (l: list funpred_def) :=
    ((Forall funpred_def_valid_type l) /\
    funpred_def_term_exists l).

(*Definition funpred_valid_type (l: list funpred_def) : Prop :=
  exists (Hl: Forall funpred_def_valid_type l),
  funpred_def_term l Hl.*)
 
(*Inductive Predicates*)

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
  | ind_def p lf => Forall (fun f => well_typed_formula s gamma f /\ 
      closed_formula f /\ valid_ind_form p f) (map snd lf)
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

End FunPredSym.

(*Put it all together*)
Definition valid_context (s : sig) (gamma: context) : Prop :=
  wf_context s gamma /\
  Forall (fun d =>
    match d with
    | datatype_def m => Forall adt_valid_type (typs m) /\ 
                           Forall (adt_inhab s gamma) (typs m) /\
                           adt_positive gamma (typs m) /\
                           valid_mut_rec m
    | recursive_def fs => (*awful hack that won't work, TODO fix*) 
                          funpred_valid_type s gamma fs
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

(*TODO: move*)
Lemma in_bool_In  {A : Type} 
(eq_dec : forall x y : A, {x = y} + {x <> y}) 
(x : A) (l : list A): in_bool eq_dec x l -> In x l.
Proof.
  intros Hin. apply (reflect_iff _ _ (in_bool_spec eq_dec x l)).
  auto.
Qed. 

(*First, prove lemmas about wf_contexts (not valid)*)
Section WFContextLemmas.

Context {s: sig} {gamma: context} (gamma_wf: wf_context s gamma).

(*TODO: move*)
Lemma adt_in_mut_alt {m: mut_adt} {a: alg_datatype}:
  reflect (In (adt_name a, ne_list_to_list (adt_constrs a)) 
  (datatypes_of_def (datatype_def m))) (adt_in_mut a m).
Proof.
  unfold adt_in_mut.
  destruct m. simpl. induction typs; simpl.
  - apply ReflectF; auto.
  - apply ssrbool.orPP; auto. destruct a0; simpl in *.
    destruct (adt_dec a (alg_def t n)) eqn : Hadteq; simpl.
    + apply ReflectT. subst. simpl. reflexivity.
    + apply ReflectF. intro Ht. inversion Ht; subst.
      apply ne_list_list_inj in H1. subst.
      destruct a; simpl in n0; contradiction.
Qed.

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
  destruct gamma_wf as [_ [_ [_ [_ [Hnodup _]]]]].
  unfold typesyms_of_context, datatypes_of_context in Hnodup.
  rewrite concat_map in Hnodup.
  rewrite map_map in Hnodup.
  rewrite NoDup_concat_iff in Hnodup.
  destruct_all. clear H.
  rewrite mut_in_ctx_eq2 in m_in1, m_in2.
  destruct (In_nth _ _ (recursive_def nil) m_in1) as [i [Hi Hith]].
  destruct (In_nth _ _ (recursive_def nil) m_in2) as [j [Hj Hjth]].
  rewrite map_length in H0.
  destruct (Nat.eq_dec i j). {
    (*If i=j, easy*)
    subst. rewrite Hith in Hjth.
    inversion Hjth; auto.
  }
  specialize (H0 i j nil (adt_name a1) Hi Hj n).
  exfalso. apply H0; clear H0.
  rewrite !map_nth_inbound with(d2:=(recursive_def [])); auto.
  rewrite Hith, Hjth.
  split; rewrite in_map_iff;
  [exists (adt_name a1, ne_list_to_list (adt_constrs a1))| 
   exists (adt_name a2, ne_list_to_list (adt_constrs a2))]; 
   split; auto; apply (ssrbool.elimT adt_in_mut_alt); auto.
Qed.

Lemma in_mutfuns (l: list funpred_def) :
  In l (mutfuns_of_context gamma) <->
  In (recursive_def l) gamma.
Proof.
  clear gamma_wf.
  induction gamma; simpl; auto; try reflexivity.
  destruct a; simpl in *.
  - split; intros; [right |]; apply IHc; auto.
    destruct H; [inversion H |]; auto.
  - split; intros; destruct_all; auto.
    + right; apply IHc; auto.
    + inversion H; subst. auto.
    + right; apply IHc; auto.
  - split; intros; [right |]; apply IHc; auto.
    destruct H; [inversion H |]; auto.
Qed.

(*The syms in the [funpred_defs_to_sns] are unique*)
Lemma funpred_defs_to_sns_NoDup (l: list funpred_def) il:
  In l (mutfuns_of_context gamma) ->
  length l = length il ->
  NoDup (map fn_sym (fst (funpred_defs_to_sns l il))) /\
  NoDup (map pn_sym (snd (funpred_defs_to_sns l il))).
Proof.
  unfold wf_context in gamma_wf.
  intros Hlen.
  destruct gamma_wf as [_ [_ [_ [_ [_ [Hwf1 Hwf2]]]]]].
  intros.
  unfold funsyms_of_context in Hwf1.
  unfold predsyms_of_context in Hwf2.
  unfold funpred_defs_to_sns; simpl; rewrite !map_map; simpl.
  pose proof (split_funpred_defs_length l) as Hlenfstsnd.
  rewrite !map_fst_fst_fst_combine; [| rewrite skipn_length | rewrite firstn_length]; try lia.
  (*TODO maybe prove equal to filter or seomthing*)
  rewrite !NoDup_concat_iff in Hwf1.
  rewrite !NoDup_concat_iff in Hwf2.
  destruct Hwf1 as [Hwf1 _ ].
  destruct Hwf2 as [Hwf2 _].
  assert (Hin: In (recursive_def l) gamma). {
    apply in_mutfuns. auto.
  }
  split; [apply Hwf1 | apply Hwf2]; rewrite in_map_iff;
  exists (recursive_def l); split; auto; simpl; clear;
  induction l; simpl; auto; destruct a; simpl; auto;
  rewrite IHl; reflexivity.
Qed.

Lemma in_fun_def l f a b:
  In (fun_def f a b) l ->
  In f (funsyms_of_def (recursive_def l)).
Proof.
  simpl; induction l; simpl; auto; intros.
  destruct H; subst; simpl; auto.
  destruct a0; simpl; try right; auto.
Qed.

Lemma in_pred_def l p a b:
  In (pred_def p a b) l ->
  In p (predsyms_of_def (recursive_def l)).
Proof.
  simpl; induction l; simpl; auto; intros.
  destruct H; subst; simpl; auto.
  destruct a0; simpl; try right; auto.
Qed.

Lemma fundef_inj (l: list funpred_def) (f: funsym)
  (a1 a2: list vsymbol) (b1 b2: term):
  In l (mutfuns_of_context gamma) ->
  In (fun_def f a1 b1) l ->
  In (fun_def f a2 b2) l ->
  a1 = a2 /\ b1 = b2.
Proof.
  unfold wf_context in gamma_wf.
  intros l_in Hin1 Hin2.
  destruct gamma_wf as [_ [_ [_ [_ [_ [Hwf1 _]]]]]].
  unfold funsyms_of_context in Hwf1.
  rewrite NoDup_concat_iff in Hwf1.
  destruct Hwf1 as [Hwf _].
  assert (Hin: In (recursive_def l) gamma). {
    apply in_mutfuns; auto.
  }
  specialize (Hwf (funsyms_of_def (recursive_def l))).
  assert (In (funsyms_of_def (recursive_def l)) (map funsyms_of_def gamma)).
    rewrite in_map_iff. exists (recursive_def l); auto.
  specialize (Hwf H); clear H.
  (*TODO: separate lemma or induction?*)
  simpl in Hwf.
  clear -Hwf Hin1 Hin2.
  induction l; [inversion Hin1 |].
  simpl in Hin1, Hin2.
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
  unfold wf_context in gamma_wf.
  intros l_in Hin1 Hin2.
  destruct gamma_wf as [_ [_ [_ [_ [_ [_ Hwf1]]]]]].
  unfold predsyms_of_context in Hwf1.
  rewrite NoDup_concat_iff in Hwf1.
  destruct Hwf1 as [Hwf _].
  assert (Hin: In (recursive_def l) gamma). {
    apply in_mutfuns; auto.
  }
  specialize (Hwf (predsyms_of_def (recursive_def l))).
  assert (In (predsyms_of_def (recursive_def l)) (map predsyms_of_def gamma)).
    rewrite in_map_iff. exists (recursive_def l); auto.
  specialize (Hwf H); clear H.
  (*TODO: separate lemma or induction?*)
  simpl in Hwf.
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

Context {s: sig} {gamma: context} (gamma_valid: valid_context s gamma).

(*These lemmas all have the same form: keep applying Forall_forall, in_map_iff,
  and similar, until we get what we want. Here we automate them*)
Ltac valid_context_tac :=
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
  unfold adt_in_mut in H.
  valid_context_tac.
  unfold valid_mut_rec in H2.
  valid_context_tac.
Qed.

Lemma adt_constr_params: forall {m: mut_adt} {a: alg_datatype}
  {c: funsym} (Hm: mut_in_ctx m gamma)
  (Ha: adt_in_mut a m)
  (Hc: constr_in_adt c a),
  s_params c = m_params m.
Proof.
  intros. unfold adt_in_mut in Ha.
  unfold constr_in_adt in Hc.
  valid_context_tac.
  unfold valid_mut_rec in H2.
  valid_context_tac. rewrite <- H3. reflexivity.
  rewrite in_bool_ne_equiv in Hc.
  apply (in_bool_In _ _ _ Hc).
Qed.

Lemma adt_constr_ret: forall {m: mut_adt} {a: alg_datatype}
  {c: funsym} (Hm: mut_in_ctx m gamma) (Ha: adt_in_mut a m) 
  (Hc: constr_in_adt c a),
  f_ret c = vty_cons (adt_name a) (map vty_var (m_params m)).
Proof.
  intros.
  (*This is an ugly hack, should change tactic so it leaves "in"
  assumptions*)
  assert (adt_mut_in_ctx a m gamma) by 
    (unfold adt_mut_in_ctx; split; assumption). 
  valid_context_tac.
  unfold adt_valid_type in H0.
  rewrite in_bool_ne_equiv in Hc.
  apply in_bool_In in Hc.
  valid_context_tac.
  rewrite H4. f_equal.
  f_equal. replace t with (adt_name ((alg_def t n))) by auto.
  apply adt_args. auto.
Qed. 

Lemma adts_names_nodups: forall {m: mut_adt}
  (Hin: mut_in_ctx m gamma),
  NoDup (map adt_name (typs m)).
Proof.
  intros. 
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
    rewrite mut_in_ctx_eq2 in Hin.
    simpl in Hin.
    destruct Hin; subst.
    + simpl in Hn1. rewrite map_map in Hn1.
      unfold adt_name. 
      assert (forall {A} (l1 l2: list A), NoDup l1 -> l1 = l2
      -> NoDup l2) by (intros; subst; auto).
      apply (H _ _ _ Hn1).
      apply map_ext. intros. destruct a; reflexivity.
    + apply IHc. rewrite mut_in_ctx_eq2. apply H. apply Hn2.
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
  intros.
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
        split; auto. apply mut_in_ctx_eq2; auto.
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

Lemma pat_has_type_valid: forall p ty,
  pattern_has_type s p ty ->
  valid_type s ty.
Proof.
  intros. induction H; try assumption; auto.
  apply valid_type_subst; auto.
Qed.

(*If a term has a type, that type is well-formed. We need the 
  [valid_pat_fmla] or else we could have an empty pattern*)
Lemma has_type_valid: forall (*s gamma*) t ty,
  (*well_typed_term s gamma t ty ->*)
  term_has_type s t ty ->
  valid_type s ty.
Proof.
  intros. induction H; try solve[constructor]; try assumption; auto.
  apply valid_type_subst; assumption.
  destruct ps. inversion H3.
  apply (H2 p); auto. left; auto. 
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
  apply (in_bool_In _ _ _ H).
Qed.
  
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