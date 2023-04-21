(*Constructing a complete interpretation - maybe call this semantics?*)

Require Export RecFun2.
Require Export IndProp.

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


(*Here, we build up a pre-interpretation through a context,
  adding function and predicate constraints as we go*)

(*Or what about this: use entire context (since we need that
  anyway) - have additional constraint (which we have)
  that says that everything in right order*)
(*Let's try this - much easier than all dep types, weakening, etc*)

(*TODO: will likely need to prove lemma that
  says these things stay same if we extend context*)

(*Need computable*)

Definition constr_get_adt (f: funsym) (m: mut_adt) : option alg_datatype :=
  find (fun x => constr_in_adt f x) (typs m).  

Lemma constr_get_adt_some f m a:
  constr_get_adt f m = Some a ->
  adt_in_mut a m /\ constr_in_adt f a.
Proof.
  unfold constr_get_adt.
  intros Hfind.
  apply find_some in Hfind.
  destruct Hfind; split; auto.
  apply In_in_bool; auto.
Qed.

Lemma constr_get_adt_none f m:
  constr_get_adt f m = None ->
  forall a, adt_in_mut a m -> ~ constr_in_adt f a.
Proof.
  intros Hfind a Hin.
  apply find_none with(x:=a) in Hfind; auto.
  rewrite Hfind; auto.
  apply in_bool_In in Hin. auto.
Qed.

Set Bullet Behavior "Strict Subproofs".

(*More convenient to have this type for function*)
Definition constr_in_mut_dec (f: funsym) (m: mut_adt) :
  Either ({a: alg_datatype | adt_in_mut a m /\ constr_in_adt f a})
    (forall a, adt_in_mut a m -> ~ constr_in_adt f a).
Proof.
  destruct (constr_get_adt f m) eqn : Hconstr.
  - apply Left. exists a. apply constr_get_adt_some; auto.
  - apply Right. apply constr_get_adt_none. auto.
Qed.

(*TODO: move probaly - need to add constrs*)
(*TODO: don't take in pi_funpred because we need to build that
  up: just take generic function, 
  then build up for each m
  
  *)
Definition funs_with_constrs {sigma: sig} {gamma: context}
  (gamma_valid: valid_context sigma gamma) (pd: pi_dom) 
  (*(pf: pi_funpred gamma_valid pd)*)
  (funs: forall (f: funsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
  domain (dom_aux pd) (funsym_sigma_ret f srts))
  (m: mut_adt) (Hm: mut_in_ctx m gamma):
  forall (f: funsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
  domain (dom_aux pd) (funsym_sigma_ret f srts) :=
  fun f srts a =>
  (*Go through each adt in m, see if f in*)
  match constr_in_mut_dec f m with
  | Left a_dat =>
    let adt := proj1_sig a_dat in
    let a_in := proj1' (proj2_sig a_dat) in
    let f_in := proj2' (proj2_sig a_dat) in
    (*TODO: require srts_len always?*)
    match (Nat.eq_dec (length srts) (length (m_params m))) with
    | left srts_len =>
      constr_rep_dom gamma_valid m Hm srts srts_len
        (dom_aux pd) adt a_in f f_in (adts pd m srts) a
    | right _ => funs f srts a
    end
  | Right f_notin => funs f srts a
  end.

Fixpoint funs_with_constrs_all_aux {sigma: sig} {gamma: context}
(gamma_valid: valid_context sigma gamma) (pd: pi_dom) 
(funs: forall (f: funsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
  domain (dom_aux pd) (funsym_sigma_ret f srts))
(l: list mut_adt)
(Hall: Forall (fun m => mut_in_ctx m gamma) l):
forall (f: funsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
  domain (dom_aux pd) (funsym_sigma_ret f srts) :=
  match l as l' return
  Forall (fun m => mut_in_ctx m gamma) l' ->
  forall (f: funsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
  domain (dom_aux pd) (funsym_sigma_ret f srts)
  with
  | nil => fun Hall => funs
  | m :: tl => fun Hall =>
    funs_with_constrs gamma_valid pd
      (funs_with_constrs_all_aux gamma_valid pd funs tl 
        (Forall_inv_tail Hall))
      m (Forall_inv Hall)
  end Hall.

Lemma mut_of_context_allin: forall gamma,
Forall (fun m : mut_adt => mut_in_ctx m gamma) (mut_of_context gamma).
Proof.
  intros.
  rewrite Forall_forall; intros.
  apply mut_in_ctx_eq. auto.
Qed.

Definition funs_with_constrs_all {sigma: sig} {gamma: context}
(gamma_valid: valid_context sigma gamma) (pd: pi_dom) 
(funs: forall (f: funsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
  domain (dom_aux pd) (funsym_sigma_ret f srts)):
forall (f: funsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
  domain (dom_aux pd) (funsym_sigma_ret f srts) :=
  funs_with_constrs_all_aux gamma_valid pd funs (mut_of_context gamma) 
  (mut_of_context_allin gamma).
Print pi_funpred.

(*Now we give the spec*)
(*Aux version: any constrs in adts in l have the correct rep*)
Lemma funs_with_constrs_all_aux_in {sigma: sig} {gamma: context}
(gamma_valid: valid_context sigma gamma) (pd: pi_dom) 
(funs: forall (f: funsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
  domain (dom_aux pd) (funsym_sigma_ret f srts))
(l: list mut_adt)
(Hall: Forall (fun m => mut_in_ctx m gamma) l)
(Hnodup: NoDup l):
forall (m : mut_adt) (a : alg_datatype) 
(c : funsym) (Hinl: In m l) (Hm : mut_in_ctx m gamma) 
(Ha : adt_in_mut a m) (Hc : constr_in_adt c a)
(srts : list sort)
(Hlens : Datatypes.length srts =
          Datatypes.length (m_params m))
(args : arg_list (domain (dom_aux pd))
          (sym_sigma_args c srts)),
(funs_with_constrs_all_aux gamma_valid pd funs l Hall) c srts args =
constr_rep_dom gamma_valid m Hm srts Hlens 
(dom_aux pd) a Ha c Hc (adts pd m srts) args.
Proof.
  induction l; simpl; intros; auto.
  destruct Hinl.
  unfold funs_with_constrs.
  destruct Hinl; subst.
  - destruct (constr_in_mut_dec c m).
    + destruct s as [a' [a_in c_in]].
      simpl.
      (*mut adts and adts share constr, so we know that
        m = a and
        a0 = a' and*)
      assert (a0 = a'). { admit. } subst.
      destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (m_params m))).
      * f_equal; try apply bool_irrelevance. apply UIP_dec. apply Nat.eq_dec.
      * contradiction.
    + exfalso. apply (n a0); auto.
  - (*In this case, need to know that not in a - by same lemma*)
    unfold funs_with_constrs.
    destruct (constr_in_mut_dec c a).
    + destruct s as [a' [a_in' c_in']].
      exfalso. (*contradiction - a = m, contradicts NoDUp - need to prove*)
      assert (a =m) by admit.
      subst.
      inversion Hnodup. auto.
    + apply IHl; auto. inversion Hnodup; subst; auto.

(*TODO: easier: find mut at same time as a, just do
  single function instead of fixpoint
  I think may not need injectivity lemma anymore
  and dont need generalization*)
(*Then proofs*)
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

(*Then use this to build initial pf from funs and preds*)
(*Then, iterate through context, find *)


Lemma funpred_with_constrs_constrs {sigma: sig} {gamma: context}
(gamma_valid: valid_context sigma gamma) (pd: pi_dom) 
(pf: pi_funpred gamma_valid pd)
(m: mut_adt) (Hm: mut_in_ctx m gamma):
forall (m : mut_adt) (a : alg_datatype) 
(c : funsym) (Hm : mut_in_ctx m gamma) 
(Ha : adt_in_mut a m) (Hc : constr_in_adt c a)
(srts : list sort)
(Hlens : Datatypes.length srts =
          Datatypes.length (m_params m))
(args : arg_list (domain (dom_aux pd))
          (sym_sigma_args c srts)),
funs c srts args =
constr_rep_dom gamma_valid m Hm srts Hlens 
  (dom_aux pd) a Ha c Hc (adts pd m srts) args



  Definition funpred_with_reps_funs (pf: pi_funpred gamma_valid pd)
  (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma)) :
  forall (f: funsym) (srts: list sort)
  (a: arg_list domain (sym_sigma_args f srts)),
  domain (funsym_sigma_ret f srts) :=

  (*Need to see if f in l and srts has right length*)
  fun f srts a => 
    match funsym_in_mutfun_dec f l with (*funsym_in_mutfun f l as b return funsym_in_mutfun f l = b -> 
      domain (funsym_sigma_ret f srts) *)
    | left f_in => 
      (*TODO: should we require srts_len always?*)
      match (Nat.eq_dec (length srts) (length (s_params f) )) with
      | left srts_len =>
        funs_rep pf f l f_in l_in srts srts_len a
      | right srts_len => (funs gamma_valid pd pf) f srts a
      end
    | right f_notin => (funs gamma_valid pd pf) f srts a
    end.

Print funpred_with_reps.

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


(*A task *)


(*First, we give an *)