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

Inductive decl : Set :=
  | type_decl : typesym -> decl (*abstract types and aliases*)
  | data_decl : mut_adt -> decl (*recursive ADTs*)
  | fparam_decl: funsym -> decl (*abstract function*)
  | pparam_decl: predsym -> decl (*abstract predicat*)
  | logic_decl : list funpred_def -> decl (*defined functions
    and predicates (possibly recursive)*)
  | ind_decl: list indpred_def -> decl (*inductive predicates*)
  | prop_decl: prop_kind -> string (*TODO: do we need name?*) ->
    formula -> decl.

(*An ordered context (which we will call an environment)
  is a list of decls, but each must be well-typed with respect
  to only the previous definitions*)
Definition env := list decl.

(*TODO: move*)
Definition indpred_name (i: indpred_def) : predsym :=
  match i with
  | ind_def p fs => p
  end.

(*TODO: in core langugae in paper, no names for indprop
  constrs. Why3 does have them, we should add *)

Definition sig_of_env_aux (e: env) : 
  (list typesym * list funsym * list predsym) :=
  fold_right (fun e acc =>
    let t := acc in
    let typs := fst (fst t) in
    let funs := snd (fst t) in
    let preds := snd t in
    match e with
    | type_decl ty => (ty :: typs, funs, preds)
    | data_decl m => 
      let tys := map adt_name (Syntax.typs m) in
      let constrs := concat (map (fun x => ne_list_to_list (adt_constrs x)) 
        (Syntax.typs m)) in
      (tys ++ typs, constrs ++ funs, preds)
    | fparam_decl f => (typs, f :: funs, preds)
    | pparam_decl p => (typs, funs, p :: preds)
    | logic_decl funpreds =>
      let newfuns := funsyms_of_def (recursive_def funpreds) in
      let newpreds := predsyms_of_def (recursive_def funpreds) in
      (typs, newfuns ++ funs, newpreds ++ preds)
    | ind_decl li => 
      let newpreds := predsyms_of_def (inductive_def li) in
      (typs, funs, newpreds ++ preds)
    | prop_decl _ _ _ => (*props do not add to the context*)
      (typs, funs, preds)
    end
  ) (nil, nil, nil) e.

Definition sig_of_env e : sig :=
  let t := sig_of_env_aux e in
  Build_sig (fst (fst t)) (snd (fst t)) (snd t).
(*Then we define a context. This is easy*)

Definition ctx_of_env (e: env) :context :=
  fold_right (fun d acc =>
  match d with
  | data_decl m =>  datatype_def m :: acc
  | logic_decl ls => recursive_def ls :: acc
  | ind_decl is => inductive_def is :: acc
  | _ => acc
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

(*TODO: move to typing*)
Lemma constr_in_one_adt {sigma: sig} {gamma: context}
  (gamma_wf: wf_context sigma gamma)
  (c: funsym) (m1 m2: mut_adt) (a1 a2: alg_datatype)
  (m_in1: mut_in_ctx m1 gamma)
  (m_in2: mut_in_ctx m2 gamma)
  (a_in1: adt_in_mut a1 m1)
  (a_in2: adt_in_mut a2 m2)
  (c_in1: constr_in_adt c a1)
  (c_in2: constr_in_adt c a2):
  a1 = a2 /\ m1 = m2.
Proof.
  (*Handle easy case first*)
  destruct (adt_dec a1 a2); subst.
  {
    split; auto. apply (@mut_adts_inj _ _ gamma_wf _ _ a2 a2); auto.
  }
  destruct gamma_wf as [_ [_ [_ [_ [_ [Hnodup _]]]]]].
  unfold funsyms_of_context in Hnodup.
  rewrite NoDup_concat_iff in Hnodup.
  (*If m1 and m2 are the same, look within def, otherwise between defs*)
  destruct (mut_adt_dec m1 m2); subst.
  - split; auto.
    destruct Hnodup as [Hnodup _].
    assert (In (datatype_def m2) gamma) by (apply mut_in_ctx_eq2; auto).
    specialize (Hnodup (funsyms_of_def (datatype_def m2))).
    assert (In (funsyms_of_def (datatype_def m2)) (map funsyms_of_def gamma)).
      rewrite in_map_iff. exists (datatype_def m2); auto.
    specialize (Hnodup H0).
    simpl in Hnodup.
    rewrite NoDup_concat_iff in Hnodup.
    rewrite map_length in Hnodup.
    (*Look across, not in, adts*)
    destruct Hnodup as [_ Hnodup].
    exfalso.
    assert (Hin1: In a1 (typs m2)) by (apply in_bool_In in a_in1; auto).
    assert (Hin2: In a2 (typs m2)) by (apply in_bool_In in a_in2; auto).
    destruct (In_nth _ _ a1 Hin1) as [i1 [Hi1 Ha1]].
    destruct (In_nth _ _ a2 Hin2) as [i2 [Hi2 Ha2]].
    (*Easy contradiction if i1 = i2*)
    destruct (Nat.eq_dec i1 i2); subst.
    {
      apply n. rewrite <- Ha1. rewrite <- Ha2. apply nth_indep. auto.
    }
    apply (Hnodup i1 i2 nil c Hi1 Hi2 n0).
    rewrite map_nth_inbound with(d2:=a1); auto.
    rewrite map_nth_inbound with(d2:=a2); auto.
    rewrite Ha1, Ha2.
    unfold constr_in_adt in c_in1, c_in2.
    destruct a1; destruct a2; simpl in *; split; apply in_bool_ne_In
    with(eq_dec:=funsym_eq_dec); auto.
  - (*This time in different m1 and m2*)
    destruct Hnodup as [_ Hnodup].
    rewrite map_length in Hnodup.
    assert (Hin1: In (datatype_def m1) gamma) by (apply mut_in_ctx_eq2; auto).
    assert (Hin2: In (datatype_def m2) gamma) by (apply mut_in_ctx_eq2; auto).
    destruct (In_nth _ _ def_d Hin1) as [i1 [Hi1 Hm1]].
    destruct (In_nth _ _ def_d Hin2) as [i2 [Hi2 Hm2]].
    destruct (Nat.eq_dec i1 i2); subst.
    {
      rewrite Hm1 in Hm2. inversion Hm2; subst; contradiction.
    }
    exfalso.
    apply (Hnodup i1 i2 nil c Hi1 Hi2 n1).
    rewrite !map_nth_inbound with (d2:=def_d); auto.
    rewrite Hm1, Hm2.
    split; [apply constr_in_adt_def with(a:=a1) |
    apply constr_in_adt_def with (a:=a2)]; auto.
Qed.

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
    apply (constr_in_one_adt (proj1' gamma_valid)) with(c:=c); auto.
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

Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma).

(*TODO: add to IndProp: extend with - maybe use interp_with_Ps
  or define separately, prove equiv - see*)
Definition upd_pf (d: def) (pf: pi_funpred gamma_valid) : pi_funpred gamma_valid :=
  match d with
  | datatype_def _ => pf
  | recursive_def fs => (funpred_with_reps pf fs _)
  | inductive_def is => (inter)


(*Then do same for funs and preds - that one needs to be in
  order because we use pf in definition, will need to show that
  adding does not affect it
But JUST build up the funs and preds reps - NOT full pf, 
prove at the end that this all works
  *)
(*Then have to prove that inj lemma*)

(*Then prove if not in, then it is the same (or else our semantics
  are not correct - should be able to set uninterpreted functions to
  anything)*)

(*Should start again**)
(*
(*Let's build each piece individually*)
Definition extend_funs pd (d: decl) 
  (funs: forall (f: funsym) (srts: list sort),
  arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
  domain (dom_aux pd) (funsym_sigma_ret f srts)) :
  forall (f: funsym) (srts: list sort),
  arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
  domain (dom_aux pd) (funsym_sigma_ret f srts).
Proof.
  destruct d.
  - exact funs.
  - (*Add constrs*)


Set Bullet Behavior "Strict Subproofs".
  (*TODO: should extend single*)
Definition extend_pf_funs (d: decl) (e: env) 
(Hval1: valid_env e)
(Hval2: valid_env (d :: e)) (*TODO: should be single condition, not valid*)
(pd: pi_dom) (pf: pi_funpred (valid_env_gamma Hval1) pd) :
pi_funpred (valid_env_gamma Hval2) pd.
destruct d.
- Print pi_funpred.
  apply (Build_pi_funpred (valid_env_gamma Hval2) pd
    (funs (valid_env_gamma Hval1) pd pf)
    (preds (valid_env_gamma Hval1) pd pf)).
  intros.
  simpl in Hm. erewrite (constrs (valid_env_gamma Hval1) pd pf).
  unfold constr_rep_dom. simpl.

    
    (preds pf)).
  unfold pi_funpred.

(*(f: funsym) (srts: list sort),
arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
domain (dom_aux pd) (funsym_sigma_ret f srts).*)
refine (match d as d' return
  forall (Hval': valid_env (d' :: e)),
  valid_env (d' :: e) -> 
  pi_funpred (valid_env_gamma Hval)
  _
  with 
  | logic_decl fs =>
    funpred_with_reps fs 
  | _ => pf
end).



  type_decl : typesym -> decl (*abstract types and aliases*)
  | data_decl : mut_adt -> decl (*recursive ADTs*)
  | fparam_decl: funsym -> decl (*abstract function*)
  | pparam_decl: predsym -> decl (*abstract predicat*)
  | logic_decl : list funpred_def -> decl (*defined functions
    and predicates (possibly recursive)*)
  | ind_decl: list indpred_def -> decl (*inductive predicates*)
  | prop_decl
  
  )
(*TODO: manual later?*)


Definition build_pf_funs (e: env) (Hval: valid_env e) :
  forall (pd: pi_dom) (pf: pi_funpred (valid_env_gamma Hval) pd)
    (f: funsym) (srts: list sort),
    arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
    domain (dom_aux pd) (funsym_sigma_ret f srts).
(*TODO: full def later?*)
Print funs_rep.
    
    )


Definition build_pf (pf: pi_funpred) : pi_funpred.
*)

(*A task *)


(*First, we give an *)