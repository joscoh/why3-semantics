(*Constructing a complete interpretation - maybe call this semantics?*)

Require Export RecFun2.
Require Export IndProp.

Set Bullet Behavior "Strict Subproofs".

(*Now we can define the complete interpretation given
  a context - one that correctly interprets recursive functions
  and predicates as well as inductive propositions*)

(*To do this, we need the notion of an ordered context which
  is iteratively constructed*)

(*TODO: maybe merge this in with original context - our
  current definition doesn't rule out using something before
  it is defined*)
(*We follow similar names as in why3's core/decl.mli*)
Inductive prop_kind : Set :=
  | Plemma  (** prove, use as a premise *)
  | Paxiom (** do not prove, use as a premise *)
  | Pgoal. (** prove, do not use as a premise *)

Inductive abstract_decl : Set :=
  | type_decl: typesym -> abstract_decl (*abstract types and aliases*)
  | fparam_decl : funsym -> abstract_decl (*abstract function*)
  | pparam_decl : predsym -> abstract_decl (*abstract predicate*).

(*We define a decl to be a concrete or abstract definition
  (TODO: use Either?)*)
Definition decl : Set := Either def abstract_decl.
(*Inductive decl : Set :=
  | def_decl: def -> decl (*ADTs, recursive functions, inductive prediates*)
  | abs_decl: abstract_decl -> decl.*)

(*Finally a why3 file/theory consists of a list of statements, 
  each of which is a decl or a lemma/axiom/goal*)

Inductive stmt : Set := 
  | decl_stmt : decl -> stmt
  | prop_stmt : prop_kind -> string -> formula -> stmt.
(*
  | prop_decl : prop_kind -> string -> formula -> decl.
  
  | type_decl : typesym -> decl 
  | data_decl : mut_adt -> decl (*recursive ADTs*)
  | fparam_decl: funsym -> decl 
  | pparam_decl: predsym -> decl 
  | logic_decl : list funpred_def -> decl (*defined functions
    and predicates (possibly recursive)*)
  | ind_decl: list indpred_def -> decl (*inductive predicates*)
  | prop_decl: prop_kind -> string (*TODO: do we need name?*) ->
    formula -> decl.*)

(*From this, we can get the environment - a list of decls
  in a specific order - and the local context*)
Definition env := list decl.
(*TODO: do we need sring?*)
Definition lctx := list (string * formula). 

(*An ordered context (which we will call an environment)
  is a list of decls, but each must be well-typed with respect
  to only the previous definitions*)

(*TODO: in core langugae in paper, no names for indprop
  constrs. Why3 does have them, we should add *)
(*Get the signature from the environment*)
Definition sig_of_env_aux (e: env):
  (list typesym * list funsym * list predsym) :=
  fold_right (fun e acc =>
  let t := acc in
  let typs := fst (fst t) in
  let funs := snd (fst t) in
  let preds := snd t in
  match e with
  | Right (type_decl ty) => (ty :: typs, funs, preds)
  | Left (datatype_def m) => 
    let tys := map adt_name (Syntax.typs m) in
    let constrs := concat (map (fun x => ne_list_to_list (adt_constrs x)) 
      (Syntax.typs m)) in
    (tys ++ typs, constrs ++ funs, preds)
  | Right (fparam_decl f) => (typs, f :: funs, preds)
  | Right (pparam_decl p) => (typs, funs, p :: preds)
  | Left (recursive_def funpreds) =>
    let newfuns := funsyms_of_def (recursive_def funpreds) in
    let newpreds := predsyms_of_def (recursive_def funpreds) in
    (typs, newfuns ++ funs, newpreds ++ preds)
  | Left (inductive_def li) => 
    let newpreds := predsyms_of_def (inductive_def li) in
    (typs, funs, newpreds ++ preds)
  end
) (nil, nil, nil) e.

Definition sig_of_env e : sig :=
  let t := sig_of_env_aux e in
  Build_sig (fst (fst t)) (snd (fst t)) (snd t).
(*Then we define a context. This is easy*)

Definition ctx_of_env (e: env) :context :=
  fold_right (fun d acc =>
    match d with
    | Left x => x :: acc
    | Right _ => acc
    end) nil e.

(*A valid environment has a valid context at each step.
  This ensures that definitions only refer to things defined
  earlier
  TODO: give efficient want to check this (NOT with checking
  everything each time)*)
Inductive valid_env : env -> Prop :=
  | VE_nil: valid_env nil
  | VE_cons: forall d tl,
    valid_env tl ->
    valid_context (sig_of_env (d :: tl)) (ctx_of_env (d :: tl)) ->
    valid_env (d :: tl).

Lemma valid_env_gamma {e}:
  valid_env e ->
  valid_context (sig_of_env e) (ctx_of_env e).
Proof.
  intros. induction H; simpl; auto.
  unfold valid_context, sig_of_env; simpl; split; auto.
  unfold wf_context. split_all; simpl; auto.
  unfold wf_sig. simpl. split; auto.
  (*TODO: separate lemma that nil is valid ctx*)
  unfold typesyms_of_context; simpl; auto.
  unfold funsyms_of_context; simpl; auto.
  unfold predsyms_of_context; simpl; auto.
  unfold typesyms_of_context; simpl; constructor.
  unfold funsyms_of_context; simpl; constructor.
  unfold predsyms_of_context; simpl; constructor.
Qed.

(*Lemma valid_env_cons {d e}:
  valid_env (d :: e) ->
  valid_env e.
Proof.*)

(** Build initial pre-interpretation of functions and
  predicates **)

(*We have assumed all along that we have a pre-interp
  which sets the constructor reps appropriately. Here
  we actually construct it, given an initial
  interpretation for all function and predicate
  symbols*)

Section BuildPreInterp.

(*Not the most efficient*)
Definition constr_get_mut_adt gamma (f: funsym): option (mut_adt * alg_datatype) :=
   let l := concat (map (fun m => combine (repeat m (length (typs m))) (typs m)) 
    (mut_of_context gamma)) in
   find (fun x => constr_in_adt f (snd x)) l.

Lemma constr_get_mut_adt_some gamma f m a:
  constr_get_mut_adt gamma f = Some (m, a) ->
  mut_in_ctx m gamma /\ adt_in_mut a m /\ constr_in_adt f a.
Proof.
  unfold constr_get_mut_adt.
  intros Hfind.
  apply find_some in Hfind.
  rewrite in_concat in Hfind.
  simpl in Hfind.
  destruct Hfind as [[l [Hinl Hinma]] f_in].
  rewrite in_map_iff in Hinl.
  destruct Hinl as [m' [Hl Hinm]]; subst.
  assert (m = m'). {
    apply in_combine_l in Hinma.
    apply repeat_spec in Hinma. subst; auto.
  }
  subst.
  apply in_combine_r in Hinma.
  split_all; auto; apply In_in_bool; auto.
Qed.

Lemma constr_get_mut_adt_none gamma f:
  constr_get_mut_adt gamma f = None ->
  forall m a, mut_in_ctx m gamma -> adt_in_mut a m -> ~ constr_in_adt f a.
Proof.
  unfold constr_get_mut_adt.
  intros Hfind.
  intros m a m_in a_in.
  apply find_none with(x:=(m, a)) in Hfind; simpl in *; auto.
  - rewrite Hfind; auto.
  - rewrite in_concat. exists (combine (repeat m (length (typs m))) (typs m)).
    split; [rewrite in_map_iff; exists m; split; auto |].
    + apply in_bool_In in m_in; auto.
    + rewrite in_combine_iff; rewrite repeat_length; auto.
      apply in_bool_In in a_in.
      destruct (In_nth _ _ a  a_in) as [i [Hi Ha]]; subst.
      exists i. split; auto.
      intros. f_equal.
      * rewrite nth_indep with(d':=m); [| rewrite repeat_length]; auto. 
        rewrite nth_repeat. auto.
      * rewrite <- Ha. apply nth_indep. auto.
Qed. 

(*More convenient to have this type for function*)
Definition constr_in_mut_dec gamma (f: funsym) :
  Either ({x: mut_adt * alg_datatype | 
    mut_in_ctx (fst x) gamma /\ adt_in_mut (snd x) (fst x) /\ 
    constr_in_adt f (snd x)})
    (forall m a, mut_in_ctx m gamma -> adt_in_mut a m -> ~ constr_in_adt f a).
Proof.
  destruct (constr_get_mut_adt gamma f) eqn : Hconstr.
  - apply Left. exists p. apply constr_get_mut_adt_some; auto.
    destruct p; auto.
  - apply Right. apply constr_get_mut_adt_none. auto.
Qed.

(*The definition - set each constructor to its rep*)
Definition funs_with_constrs {sigma: sig} {gamma: context}
  (gamma_valid: valid_context sigma gamma) (pd: pi_dom) 
  (*(pf: pi_funpred gamma_valid pd)*)
  (funs: forall (f: funsym) (srts: list sort)
  (arg: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
  domain (dom_aux pd) (funsym_sigma_ret f srts)):
  forall (f: funsym) (srts: list sort)
  (arg: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
  domain (dom_aux pd) (funsym_sigma_ret f srts) :=
  fun f srts arg =>
  match constr_in_mut_dec gamma f with
  | Left adt_dat =>
    let m := fst (proj1_sig adt_dat) in
    let a := snd (proj1_sig adt_dat) in
    let m_in := proj1' (proj2_sig adt_dat) in
    let a_in := proj1' (proj2' (proj2_sig adt_dat)) in
    let f_in := proj2' (proj2' (proj2_sig adt_dat)) in
     (*TODO: require srts_len always?*)
     match (Nat.eq_dec (length srts) (length (m_params m))) with
     | left srts_len =>
       constr_rep_dom gamma_valid m m_in srts srts_len
         (dom_aux pd) a a_in f f_in (adts pd m srts) arg
     | right _ => funs f srts arg
     end
  | Right f_notin => funs f srts arg
  end.


(*Need 2 results: constrs are correct and everything else
  is from [funs]*)

(*First, all constrs are correct*)
Lemma funs_with_constrs_constrs {sigma: sig} {gamma: context}
  (gamma_valid: valid_context sigma gamma) (pd: pi_dom) 
  (funs: forall (f: funsym) (srts: list sort)
    (arg: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
    domain (dom_aux pd) (funsym_sigma_ret f srts)):
  forall (m : mut_adt) (a : alg_datatype) 
  (c : funsym) (Hm : mut_in_ctx m gamma) 
  (Ha : adt_in_mut a m) (Hc : constr_in_adt c a)
  (srts : list sort)
  (Hlens : Datatypes.length srts =
            Datatypes.length (m_params m))
  (args : arg_list (domain (dom_aux pd))
            (sym_sigma_args c srts)),
  (funs_with_constrs gamma_valid pd funs) c srts args =
  constr_rep_dom gamma_valid m Hm srts Hlens 
  (dom_aux pd) a Ha c Hc (adts pd m srts) args.
Proof.
  intros.
  unfold funs_with_constrs.
  destruct (constr_in_mut_dec gamma c).
  2: {
    exfalso. apply (n m a); auto.
  }
  destruct s as [[m' a'] [m_in [a_in c_in]]]. simpl in *.
  (*Now we need to prove that m=m' and a=a'*)
  assert (a' = a /\ m' = m). {
    apply (constr_in_one_adt gamma_valid) with(c:=c); auto.
  }
  destruct H; subst.
  destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (m_params m)));
  [|contradiction].
  assert (Hlens = e). apply UIP_dec. apply Nat.eq_dec. 
  subst.
  replace m_in with Hm by apply bool_irrelevance.
  replace a_in with Ha by apply bool_irrelevance.
  replace c_in with Hc by apply bool_irrelevance.
  reflexivity.
Qed.

(*And for everything else, use funs*)
Lemma funs_with_constrs_notin {sigma: sig} {gamma: context}
  (gamma_valid: valid_context sigma gamma) (pd: pi_dom) 
    (funs: forall (f: funsym) (srts: list sort)
    (arg: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
  domain (dom_aux pd) (funsym_sigma_ret f srts)):
  forall (f: funsym) srts arg,
    (forall (m: mut_adt) (a: alg_datatype),
      mut_in_ctx m gamma ->
      adt_in_mut a m ->
      ~constr_in_adt f a) ->
    funs_with_constrs gamma_valid pd funs f srts arg =
  funs f srts arg.
Proof.
  intros.
  unfold funs_with_constrs.
  destruct (constr_in_mut_dec gamma f); auto.
  destruct s as [[m a] [m_in [a_in f_in]]]; simpl in *.
  exfalso. apply (H m a); auto.
Qed.

(*Now build a pi_funpred from a funs and preds function*)
Definition mk_pi_funpred {sigma: sig} {gamma: context}
  (gamma_valid: valid_context sigma gamma) (pd: pi_dom)
  (funs: forall (f: funsym) (srts: list sort)
    (arg: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
    domain (dom_aux pd) (funsym_sigma_ret f srts))
  (preds: forall (p: predsym) (srts: list sort)
    (arg: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)),
    bool):
  pi_funpred gamma_valid pd :=
  Build_pi_funpred gamma_valid pd (funs_with_constrs gamma_valid pd funs)
    preds (funs_with_constrs_constrs gamma_valid pd funs).

End BuildPreInterp.

(*Now, we need to add reps for recursive functions and predicates
  and inductive predicates. We need to do this in order so that
  we mantain our invariants (since these defs can depend on previously-
  defined function and predicates)*)
Section BuildInterp.

Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
  (pd: pi_dom).

(*Update a pf with reps for a single def*)
Definition upd_pf (d: def) (pf: pi_funpred gamma_valid pd) (Hin: In d gamma) : 
  pi_funpred gamma_valid pd :=
  match d as d' return In d' gamma -> pi_funpred gamma_valid pd with
  | datatype_def _ => fun _ => pf
  | recursive_def fs => fun Hin => 
    (funpred_with_reps gamma_valid pf fs ((proj2' (in_mutfuns fs)) Hin))
  | inductive_def is => fun Hin =>  (pf_with_indprop gamma_valid pd pf 
    (get_indpred is) (in_inductive_ctx _ is Hin))
  end Hin.

Fixpoint upd_pf_multi (l: list def) (pf: pi_funpred gamma_valid pd)
  (Hallin: Forall (fun x => In x gamma) l):
  pi_funpred gamma_valid pd :=
  match l as l' return Forall (fun x => In x gamma) l' ->
    pi_funpred gamma_valid pd
  with
  | nil => fun _ => pf
  | d :: tl => fun Hall =>
    upd_pf d (upd_pf_multi tl pf (Forall_inv_tail Hall)) (Forall_inv Hall)
  end Hallin.

(*Now we want to prove the spec for this - we prove that
  everything is mapped to its rep *under the 
  current interpretation* - this is more complicated than it
  seems, since each is defined with a previous interpretation;
  we must prove equivalence*)

Lemma in_mutfuns_sub {l: list def}
(Hallin: Forall (fun x => In x gamma) l)
{fs} (fs_in: In (recursive_def fs) l):
In fs (mutfuns_of_context gamma).
Proof.
  rewrite in_mutfuns.
  rewrite Forall_forall in Hallin.
  apply Hallin; auto.
Qed.

(*TODO: do we care about this for ADTs?*)
(*

Definition ts_in_constr (ts: typesym) (f: funsym) : bool :=
  existsb (fun x => typesym_in ts x) (s_args f).


Definition ts_in_def (ts: typesym) (d: def) : bool :=
  match d with
  | datatype_def m =>
    in_bool typesym_eq_dec ts (map adt_name (typs m)) ||
    existsb (ts_in_constr ts) (concat (map (fun x => ne_list_to_list (adt_constrs x)) (typs m)))
  | recursive_def 
  end.*)
(*A funsym occurs in the body of a recursive function or constructor*)
Definition funsym_in_def (f: funsym) (d: def) : bool :=
  match d with
  | datatype_def _ => false
  | recursive_def fs => 
    existsb (fun x =>
      match x with
      | fun_def _ _ t => funsym_in_tm f t
      | pred_def _ _ fmla => funsym_in_fmla f fmla
      end) fs
  | inductive_def is =>
    existsb (funsym_in_fmla f) (concat (map snd (map indpred_def_to_indpred is)))
  end.

Definition predsym_in_def (p: predsym) (d: def) : bool :=
match d with
| datatype_def _ => false
| recursive_def fs => 
  existsb (fun x =>
    match x with
    | fun_def _ _ t => predsym_in_tm p t
    | pred_def _ _ fmla => predsym_in_fmla p fmla
    end) fs
| inductive_def is =>
  existsb (predsym_in_fmla p) (concat (map snd (map indpred_def_to_indpred is)))
end.

(*We need that the contexts are ordered; a definition cannot
  refer to anything that comes later (mutual definitions do not count)*)
Inductive ctx_ordered : list def -> Prop :=
  | ordered_nil : ctx_ordered nil
  | ordered_adt: forall m tl,
    ctx_ordered tl ->
    (*Here, we don't care for now - TODO SEE*)
    ctx_ordered (datatype_def m :: tl)
  | ordered_rec: forall fs tl,
    ctx_ordered tl ->
    (forall f d,
      funsym_in_mutfun f fs ->
      In d tl ->
      ~ funsym_in_def f d
      ) ->
    (forall p d,
      predsym_in_mutfun p fs ->
      In d tl ->
      ~ predsym_in_def p d) ->
    ctx_ordered (recursive_def fs :: tl)
  | ordered_indprop: forall (is: list indpred_def) tl,
    ctx_ordered tl ->
    (forall p d,
      p_in_indpred p is ->
      In d tl ->
      ~ predsym_in_def p d
    ) ->
    ctx_ordered ((inductive_def is) :: tl).
  
    (*Neither the types nor constructors defined in
      m occur in the tl*)

Lemma upd_pf_multi_recfun (l: list def) (pf: pi_funpred gamma_valid pd)
(Hallin: Forall (fun x => In x gamma) l)
(Hnodupl: NoDup l)
(Hordl: ctx_ordered l)
fs (fs_in: In (recursive_def fs) l)
(f: funsym) (args: list vsymbol) (body: term)
(f_in: In (fun_def f args body) fs)
(srts: list sort) (srts_len: length srts = length (s_params f))
(a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts))
(vt: val_typevar)
(vv: val_vars pd vt):
funs gamma_valid pd (upd_pf_multi l pf Hallin) f srts a =
dom_cast _ (funs_cast gamma_valid vt (recfun_in_funsyms (in_mutfuns_sub Hallin fs_in) (fun_in_mutfun f_in)) srts_len) (
  term_rep gamma_valid pd (vt_with_args vt (s_params f) srts)
    (upd_pf_multi l pf Hallin) 
    (val_with_args _ _ (upd_vv_args pd vt vv (s_params f) srts (eq_sym srts_len)
    (s_params_Nodup _)) args a)
    body (f_ret f) (f_body_type gamma_valid (in_mutfuns_sub Hallin fs_in) f_in)
).
Proof.
  generalize dependent (in_mutfuns_sub Hallin fs_in).
  intros fs_in'.
  generalize dependent Hallin.
  induction l; simpl; intros; [destruct fs_in |].
  simpl in fs_in.
  inversion Hnodupl; subst; clear Hnodupl.
  destruct fs_in; subst.
  - (*The result for the current addition follows from
      [funs_rep_spec]*) simpl.
    unfold funpred_with_reps_funs.
    set (finm:=fun_in_mutfun f_in).
    destruct (funsym_in_mutfun_dec f fs); try contradiction.
    destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (s_params f)));
    try contradiction.
    assert (i = fun_in_mutfun f_in). apply bool_irrelevance.
    rewrite H.
    rewrite funs_rep_spec with (vt:=vt)(vv:=vv).
    assert (srts_len = e) by (apply UIP_dec; apply Nat.eq_dec).
    assert (fs_in' = (proj2' (in_mutfuns fs) (Forall_inv Hallin)))
      by apply proof_irrel.
    subst.
    apply dom_cast_eq.
  - (*Now we show the inductive case - here, we need to know
    that we haven't modified any fun or pred definition already
    used*)
    destruct a0; simpl; auto.
    + (*alg datatype - easy*)
      inversion Hordl; auto.
    + (*Other recursive def*)
      inversion Hordl; subst.
      rewrite funpred_with_reps_funs_notin.
      rewrite (IHl); auto.
      f_equal.
      apply tm_change_pf.
      * intros. simpl.
        repeat (apply functional_extensionality_dep; intros).
        rewrite funpred_with_reps_preds_notin; auto.
        (*Here, we use the ordering assumption*)
        intro Hpin.
        apply (H6 p (recursive_def fs)); auto.
        unfold predsym_in_def.
        bool_to_prop. exists (fun_def f args body). auto.
      * intros. simpl.
        repeat (apply functional_extensionality_dep; intros).
        rewrite funpred_with_reps_funs_notin; auto.
        intro Hpin.
        apply (H5 f0 (recursive_def fs)); auto.
        unfold funsym_in_def.
        bool_to_prop. exists (fun_def f args body). auto.
      * intros Hinf.
        assert (l0 = fs). {
          apply (recfun_not_twice gamma_valid) with (f:=f); auto;
          try (rewrite Forall_forall in Hallin; apply Hallin; simpl); auto.
          apply (fun_in_mutfun f_in).
        }
        subst. contradiction.
    + (*inductive def*)
      inversion Hordl; subst.
      rewrite IHl; auto.
      f_equal.
      apply tm_change_pf; simpl; auto.
      (*Only the preds case is interesting*)
      intros. simpl.
      repeat (apply functional_extensionality_dep; intros).
      rewrite pf_with_indprop_preds_notin; auto.
      (*Here, we use the ordering assumption*)
      intro Hpin.
      apply (H5 p (recursive_def fs)); auto.
      unfold pred_in_indpred in Hpin.
      unfold p_in_indpred.
      apply in_bool_In in Hpin; auto.
      unfold predsym_in_def.
      bool_to_prop. exists (fun_def f args body). auto.
Qed.

(*Now we can prove the spec for recursive predicates:*)
Lemma upd_pf_multi_recpred (l: list def) (pf: pi_funpred gamma_valid pd)
(Hallin: Forall (fun x => In x gamma) l)
(Hnodupl: NoDup l)
(Hordl: ctx_ordered l)
fs (fs_in: In (recursive_def fs) l)
(p: predsym) (args: list vsymbol) (body: formula)
(p_in: In (pred_def p args body) fs)
(srts: list sort) (srts_len: length srts = length (s_params p))
(a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts))
(vt: val_typevar)
(vv: val_vars pd vt):
preds gamma_valid pd (upd_pf_multi l pf Hallin) p srts a =
formula_rep gamma_valid pd (vt_with_args vt (s_params p) srts)
  (upd_pf_multi l pf Hallin) 
  (val_with_args _ _ (upd_vv_args pd vt vv (s_params p) srts (eq_sym srts_len)
  (s_params_Nodup _)) args a)
  body (p_body_type gamma_valid (in_mutfuns_sub Hallin fs_in) p_in).
Proof.
  generalize dependent (in_mutfuns_sub Hallin fs_in).
  intros fs_in'.
  generalize dependent Hallin.
  induction l; simpl; intros; [destruct fs_in |].
  simpl in fs_in.
  inversion Hnodupl; subst; clear Hnodupl.
  destruct fs_in; subst.
  - (*The result for the current addition follows from
      [preds_rep_spec]*) simpl.
    unfold funpred_with_reps_preds.
    set (pinm:=pred_in_mutfun p_in).
    destruct (predsym_in_mutfun_dec p fs); try contradiction.
    destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (s_params p)));
    try contradiction.
    assert (i = pred_in_mutfun p_in). apply bool_irrelevance.
    rewrite H.
    rewrite preds_rep_spec with (vt:=vt)(vv:=vv).
    assert (srts_len = e) by (apply UIP_dec; apply Nat.eq_dec).
    assert (fs_in' = (proj2' (in_mutfuns fs) (Forall_inv Hallin)))
      by apply proof_irrel.
    subst.
    reflexivity.
  - (*Now we show the inductive case - here, we need to know
    that we haven't modified any fun or pred definition already
    used*)
    destruct a0; simpl; auto.
    + (*alg datatype - easy*)
      inversion Hordl; auto.
    + (*Other recursive def*)
      inversion Hordl; subst.
      rewrite funpred_with_reps_preds_notin.
      rewrite (IHl); auto.
      apply fmla_change_pf.
      * intros. simpl.
        repeat (apply functional_extensionality_dep; intros).
        rewrite funpred_with_reps_preds_notin; auto.
        (*Here, we use the ordering assumption*)
        intro Hpin.
        apply (H6 p0 (recursive_def fs)); auto.
        unfold predsym_in_def.
        bool_to_prop. exists (pred_def p args body). auto.
      * intros. simpl.
        repeat (apply functional_extensionality_dep; intros).
        rewrite funpred_with_reps_funs_notin; auto.
        intro Hpin.
        apply (H5 fs0 (recursive_def fs)); auto.
        unfold funsym_in_def.
        bool_to_prop. exists (pred_def p args body). auto.
      * intros Hinf.
        assert (l0 = fs). {
          apply (recpred_not_twice gamma_valid) with (p:=p); auto;
          try (rewrite Forall_forall in Hallin; apply Hallin; simpl); auto.
          apply (pred_in_mutfun p_in).
        }
        subst. contradiction.
    + (*inductive def*)
      inversion Hordl; subst.
      rewrite pf_with_indprop_preds_notin.
      rewrite IHl; auto.
      apply fmla_change_pf; simpl; auto.
      (*Only the preds case is interesting*)
      intros. simpl.
      repeat (apply functional_extensionality_dep; intros).
      rewrite pf_with_indprop_preds_notin; auto.
      (*Here, we use the ordering assumption*)
      intro Hpin.
      apply (H5 p0 (recursive_def fs)); auto.
      unfold pred_in_indpred in Hpin.
      unfold p_in_indpred.
      apply in_bool_In in Hpin; auto.
      unfold predsym_in_def.
      bool_to_prop. exists (pred_def p args body). auto.
      apply (recpred_not_indpred gamma_valid) with(l1:=fs); auto;
      try (rewrite Forall_forall in Hallin; apply Hallin; simpl; auto).
      apply (pred_in_mutfun p_in).
Qed.

Lemma indpreds_of_sub {l1 l2} (Hall: Forall (fun x => In x l2) l1)
  {ps}
  (ps_in: In ps (indpreds_of_context l1)):
  In ps (indpreds_of_context l2).
Proof.
  apply in_indpreds_of_context in ps_in.
  destruct ps_in as [d [Hind Hps]]; subst.
  apply in_inductive_ctx.
  rewrite Forall_forall in Hall; apply Hall; auto.
Qed.

(*TODO: move these 2 to typing*)
Lemma pred_in_indpred_spec p l:
  pred_in_indpred p (get_indpred l) <->
  In p (predsyms_of_def (inductive_def l)).
Proof.
  simpl. unfold get_indpred, pred_in_indpred.
  rewrite (reflect_iff _ _ (in_bool_spec predsym_eq_dec _ _)).
  induction l; simpl; [split; intros; auto |].
  unfold is_true in *. bool_to_prop.
  rewrite IHl. split; intros [Hp | Htl]; auto; left;
  destruct a; auto.
Qed.

Lemma indpred_not_twice p l1 l2:
  In (inductive_def l1) gamma ->
  In (inductive_def l2) gamma ->
  pred_in_indpred p (get_indpred l1) ->
  pred_in_indpred p (get_indpred l2) ->
  l1 = l2.
Proof.
  intros.
  destruct gamma_valid as [Hwf _].
  unfold wf_context in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ [_ Hnodup]]]]]].
  unfold predsyms_of_context in Hnodup.
  rewrite NoDup_concat_iff in Hnodup.
  destruct Hnodup as [_ Hn].
  rewrite map_length in Hn.
  destruct (In_nth _ _ def_d H) as [i1 [Hi1 Hl1]].
  destruct (In_nth _ _ def_d H0) as [i2 [Hi2 Hl2]].
  destruct (Nat.eq_dec i1 i2); subst.
  {
    rewrite Hl1 in Hl2. inversion Hl2; auto.
  }
  exfalso. apply (Hn _ _ nil p Hi1 Hi2 n).
  rewrite !map_nth_inbound with(d2:=def_d); auto.
  rewrite Hl1, Hl2.
  split; apply pred_in_indpred_spec; auto.
Qed.

(*NOTE: requires (only) [indpred_rep_change_pf]
  and [pf_with_indprop_preds_notin]
*)

(*We handle IndProps a bit differently; showing that they
  equal their rep instead. We do this because for recursive functions
  and predicates, it is much easier to work with term/formula
  rep than the funrep, which is big and complicated. We do not
  have such an issue for inductive predicates*)
Lemma upd_pf_multi_indprop (l: list def) (pf: pi_funpred gamma_valid pd)
  (Hallin: Forall (fun x => In x gamma) l)
  (Hnodupl: NoDup l)
  (Hordl: ctx_ordered l)
  (ps: list (predsym * list formula))
  (ps_in: In ps (indpreds_of_context l))
  (p: predsym)
  (p_in: pred_in_indpred p ps)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)):
  preds gamma_valid pd (upd_pf_multi l pf Hallin) p srts a =
  indpred_rep_full gamma_valid pd (upd_pf_multi l pf Hallin)
    ps (indpreds_of_sub Hallin ps_in) p p_in srts a.
Proof.
  generalize dependent (indpreds_of_sub Hallin ps_in).
  intros ps_in'.
  generalize dependent Hallin.
  induction l; simpl; intros; [destruct ps_in |].
  simpl in ps_in.
  inversion Hnodupl; subst; clear Hnodupl.
  destruct a0; simpl in ps_in.
  - (*if first is datatype, easy*)
    simpl. inversion Hordl; subst. apply IHl; auto.
  - (*If first is recursive, use valid context uniqueness*)
    destruct (in_indpreds_of_context _ ps_in) as [d [d_in Hps]]; subst.
    simpl. inversion Hordl; subst.
    rewrite funpred_with_reps_preds_notin.
    2: {
      intros Hin.
      apply (recpred_not_indpred gamma_valid p l0 d); auto;
      rewrite Forall_forall in Hallin;
      apply Hallin; simpl; auto.
    }
    rewrite IHl; auto.
    apply indpred_rep_change_pf.
    + (*Need to show that none of these functions show up
      in pred definition, from ordered context*)
      intros. simpl.
      rewrite funpred_with_reps_funs_notin; auto.
      intros Hin.
      apply (H4 fs (inductive_def d)); auto.
      simpl. bool_to_prop.
      exists fmla. auto.
    + (*and for preds*)
      intros. simpl.
      rewrite funpred_with_reps_preds_notin; auto.
      intros Hin.
      apply (H5 ps (inductive_def d)); auto.
      simpl. bool_to_prop. exists fmla. auto.
  - (*For inductive def, 2 cases*)
    destruct ps_in.
    + fold indpred_def_to_indpred in H. 
      assert (ps = get_indpred l0). { subst; auto. }
      clear H. subst.
      simpl.
      unfold pf_with_indprop_preds.
      destruct (pred_in_indpred_dec p (get_indpred l0)); try contradiction.
      destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (s_params p)));
      try contradiction.
      assert (i = p_in) by apply bool_irrelevance. subst.
      assert (ps_in' = (in_inductive_ctx gamma l0 (Forall_inv Hallin))). {
        apply proof_irrel. (*TODO: bool?*)
      }
      subst.
      apply indpred_rep_change_pf; auto. 
      (*Now prove that no predicate in the formula changes*)
      intros. simpl.
      rewrite pf_with_indprop_preds_notin; auto.
      intros Hin. apply H3. apply in_bool_In in Hin; auto.
    + (*Recursive case for indpreds*)
      rename H into ps_in.
      destruct (in_indpreds_of_context _ ps_in) as [d [d_in Hps]]; subst.
      simpl. inversion Hordl; subst.
      rewrite pf_with_indprop_preds_notin.
      2: {
        intros Hin.
        assert (l0 = d); [|subst; contradiction].
        apply (indpred_not_twice p l0 d); auto;
        rewrite Forall_forall in Hallin;
        apply Hallin; simpl; auto.
      }
      rewrite IHl; auto.
      apply indpred_rep_change_pf; auto. 
      (*Show no preds appear in body*)
      intros. simpl.
      rewrite pf_with_indprop_preds_notin; auto.
      intros Hin.
      apply (H4 ps (inductive_def d)); auto.
      simpl. bool_to_prop. exists fmla. auto.
Qed.

End BuildInterp.

(*The complete interp: starting with an interpretation for
  uninterpreted functions and predicates, we add all definitions
  in the context*)

Section FullInterp.

(*Some lemmas*)
Lemma all_in_refl {A: Type} (l: list A):
  Forall (fun x => In x l) l.
Proof.
  rewrite Forall_forall; intros; auto.
Qed.

Lemma indprop_fmla_valid {sigma gamma}
  (gamma_valid: valid_context sigma gamma) 
  {l: list (predsym * list formula)}
  (l_in: In l (indpreds_of_context gamma))
  {p: predsym} {fs: list formula}
  (p_in: In (p, fs) l)
  {f: formula}
  (f_in: In f fs):
  valid_formula sigma f.
Proof.
  pose proof (in_indpred_valid gamma_valid l_in).
  rewrite Forall_forall in H.
  assert (In fs (map snd l)). rewrite in_map_iff.
  exists (p, fs); auto.
  specialize (H _ H0).
  rewrite Forall_forall in H.
  apply H; auto.
Qed.

(*TODO: move when finish*)
(*Sort of trivial, but a well-formed context has no dups*)
(*
Lemma wf_ctx_Nodup:
  NoDup gamma.
Proof.
  unfold wf_context in gamma_wf.
  destruct gamma_wf as [_ [_ [_ [_ [Hn1 [Hn2 Hn3]]]]]].
  clear -gamma Hn1 Hn2 Hn3.
  unfold typesyms_of_context in Hn1.
  unfold funsyms_of_context in Hn2.
  unfold predsyms_of_context in Hn3.
  induction gamma; simpl in *; constructor; auto.
  - intros Hina. destruct a; simpl in *.
    + rewrite NoDup_app_iff in Hn2.
      destruct Hn2.
      (*ugh, prob need assumption about non-trivial*)
      (*TODO: elsehwere*)
    
    rewrite NoDup_concat_iff in Hn2.
    
    
    intro
*)

(*We can define what it means for an interpretation to be complete*)
Definition full_interp {sigma gamma} 
(gamma_valid: valid_context sigma gamma)
(pd: pi_dom)
(pf: pi_funpred gamma_valid pd) : Prop :=
(*Recursive functions are equal (with a cast) to their body, 
  under the valuation where the type arguments are mapped to srts 
  and the arguments are mapped to a, the arg list*)
(forall (fs: list funpred_def)
  (fs_in: In fs (mutfuns_of_context gamma))
  (f: funsym) (args: list vsymbol) (body: term)
  (f_in: In (fun_def f args body) fs)
  (srts: list sort) (srts_len: length srts = length (s_params f))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts))
  (vt: val_typevar)
  (vv: val_vars pd vt),
  funs gamma_valid pd pf f srts a =
  dom_cast _ (funs_cast gamma_valid vt (recfun_in_funsyms fs_in (fun_in_mutfun f_in)) srts_len) (
    term_rep gamma_valid pd (vt_with_args vt (s_params f) srts)
      pf
      (val_with_args _ _ (upd_vv_args pd vt vv (s_params f) srts (eq_sym srts_len)
      (s_params_Nodup _)) args a)
      body (f_ret f) (f_body_type gamma_valid fs_in f_in)
    )
) /\
(*Recursive predicates are equal to their body, under the valuation
  where the type arguments are mapped to srts and the arguments
  are mapped to a, the arg list*)
(forall (fs: list funpred_def)
  (fs_in: In fs (mutfuns_of_context gamma))
  (p: predsym) (args: list vsymbol) (body: formula)
  (p_in: In (pred_def p args body) fs)
  (srts: list sort) (srts_len: length srts = length (s_params p))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts))
  (vt: val_typevar)
  (vv: val_vars pd vt),
  preds gamma_valid pd pf p srts a =
  formula_rep gamma_valid pd (vt_with_args vt (s_params p) srts)
    pf
    (val_with_args _ _ (upd_vv_args pd vt vv (s_params p) srts (eq_sym srts_len)
    (s_params_Nodup _)) args a)
    body (p_body_type gamma_valid fs_in p_in)
) /\
(*Inductive predicates part 1: all constructors are true under all 
  valuations sending the type parameters to the srts*)
(forall (l: list (predsym * list formula))
  (l_in: In l (indpreds_of_context gamma))
  (p: predsym) (fs: list formula)
  (p_in: In (p, fs) l)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (vt: val_typevar)
  (vv: val_vars pd (vt_with_args vt (s_params p) srts))
  (f: formula)
  (f_in: In f fs),
  formula_rep gamma_valid pd 
    (vt_with_args vt (s_params p) srts) pf vv f 
    (*Typing proof*)
    (indprop_fmla_valid gamma_valid l_in p_in f_in)
) /\
(*Inductive predicates part 2: this is the least predicate
  such that the constructors hold
  TODO: is there a better way to express this?*)
(forall (l: list (predsym * list formula))
  (l_in: In l (indpreds_of_context gamma))
  (p: predsym)
  (p_in: In p (map fst l))
  (fs: list formula)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts))
  (vt: val_typevar)
  (vv: val_vars pd (vt_with_args vt (s_params p) srts)),

  (*For any other set of predicates p1...pn*)
  forall (Ps: hlist
    (fun p' : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
    (map fst l)),
  (*If the constructors hold when ps -> Ps (ith of ps -> ith of Ps)*)
  (forall (fs : list formula) (Hform : Forall (valid_formula sigma) fs),
    In fs (map snd l) ->
      iter_and (map is_true (dep_map
        (formula_rep gamma_valid pd 
        (vt_with_args vt (s_params p) srts) 
        (interp_with_Ps gamma_valid pd pf (map fst l) Ps) vv) fs Hform))) ->
  (*Then preds p fs x -> P x*) 
  preds gamma_valid pd pf p srts a ->
  get_hlist_elt predsym_eq_dec Ps p 
    (In_in_bool predsym_eq_dec _ _ p_in) srts a
).

(*Now we construct the interpretation; we prove that
  it satisfies all of the conditions of [full_interp]*)

(*Here, we use an env, because we need it to be correctly
  ordered*)
Context {e: env} (e_val: valid_env e) (pd: pi_dom).

Notation gamma := (ctx_of_env e).
Notation gamma_valid := (valid_env_gamma e_val).

Definition full_pf funs preds : 
  pi_funpred gamma_valid pd :=
  upd_pf_multi gamma_valid pd gamma
    (*start with the ADT constructors, add all defs in gamma*)
    (mk_pi_funpred gamma_valid pd funs preds)
    (all_in_refl gamma).

(*And the spec: first, it is a full_interp*)
Theorem full_pf_interp funs preds :
  full_interp gamma_valid pd (full_pf funs preds).
Proof.
  assert (Hnodup: NoDup gamma). admit. (*TODO: preove*)
  assert (Hord: ctx_ordered gamma). admit. (*TODO: harder proof*)
  unfold full_interp. split_all.
  - intros. unfold full_pf.
    rewrite (upd_pf_multi_recfun gamma_valid pd gamma
    (mk_pi_funpred gamma_valid pd funs preds) (all_in_refl gamma) Hnodup
    Hord fs (proj1 (in_mutfuns_spec fs gamma) fs_in) f args
    body f_in srts srts_len a vt vv).
    (*Need proof irrelevance - TODO: bool proofs?*)
    assert ((in_mutfuns_sub (all_in_refl gamma)
    (proj1 (in_mutfuns_spec fs gamma) fs_in)) = fs_in) by
    (apply proof_irrel).
    rewrite H. apply dom_cast_eq.
  - intros. unfold full_pf.
    rewrite (upd_pf_multi_recpred gamma_valid pd gamma
    (mk_pi_funpred gamma_valid pd funs preds) (all_in_refl gamma) Hnodup
    Hord fs (proj1 (in_mutfuns_spec fs gamma) fs_in) p args
    body p_in srts srts_len a vt vv).
    (*Again, proof irrel*)
    f_equal. f_equal. apply proof_irrel.
  - intros. unfold full_pf. 
    eapply indpred_constrs_true_val with(indpred:=l).
    + apply (in_indpred_valid_ind_form gamma_valid); auto.
    + apply (in_indpred_positive gamma_valid); auto.
    + apply (in_indpred_closed gamma_valid); auto.
    + intros.
      (*Here, use fact that preds sets all to indprop_rep*)
      apply upd_pf_multi_indprop; auto.
    + apply p_in.
    + auto.
    + apply srts_len.
    + apply (in_indpred_params gamma_valid); auto.
    + assert (Hinp: pred_in_indpred p l). {
        apply In_in_bool. rewrite in_map_iff. exists (p, fs); auto.
      }
      pose proof (in_indpred_unif gamma_valid l_in Hinp).
      rewrite Forall_concat in H.
      rewrite Forall_map in H.
      rewrite Forall_forall in H.
      specialize (H _ p_in).
      auto.
    + apply (in_indpred_typevars gamma_valid); auto.
      apply In_in_bool. rewrite in_map_iff. exists (p, fs); auto.
    + apply vt_with_args_vt_eq; auto. apply s_params_Nodup.
      Unshelve. auto.
  - (*And the least predicate proof*)
    intros.
    eapply (indpred_least_pred_val gamma_valid _ _ 
      (vt_with_args vt (s_params p) srts) vv); auto.
    + apply vt_with_args_vt_eq; auto. apply s_params_Nodup.
    + apply (in_indpred_typevars gamma_valid); auto.
      apply In_in_bool; auto. 
    + rewrite Forall_concat. apply (in_indpred_closed gamma_valid); auto.
    + (*Here, use fact that preds sets all to indprop_rep*)
      unfold full_pf in *.
      rewrite upd_pf_multi_indprop with(ps:=l)(ps_in:=l_in)
        (p_in:=(In_in_bool predsym_eq_dec p (map fst l) p_in)) in H0; auto.
      apply H0.
Admitted.

End FullInterp.
