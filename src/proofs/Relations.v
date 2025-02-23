From Proofs Require Import Task AssocList Alpha.
Require Import TyDefs TyFuncs NumberDefs TermDefs TermFuncs DeclDefs TheoryDefs TaskDefs TransDefs.

(*Define "eval" function: takes augmented type/term/etc, produces core type/term/etc*)
Section Eval.

(*Idents*)

(*An ident is evaluated to its name followed by its id (which is always positive)*)
Definition eval_ident (i: ident) : string :=
  (id_string i) ++ (GenElts.nat_to_string (Z.to_nat (id_tag i))).

(*Types*)

Definition eval_typevar (t: tvsymbol) : typevar :=
  eval_ident (tv_name t).

Definition eval_typesym (t: tysymbol_c) : typesym :=
  Types.mk_ts (eval_ident (ts_name_of t)) (map eval_typevar (ts_args_of t)).

(*NOTE: ignore annotations (type_def)*)

Fixpoint eval_ty (t: ty_c) : vty :=
  if (ty_eqb t ty_int) then vty_int else
  if (ty_eqb t ty_real) then vty_real else
  match (ty_node_of t) with
  | Tyvar v => vty_var (eval_typevar v)
  | Tyapp ts tys => vty_cons (eval_typesym ts) (map eval_ty tys)
  end.

(*Terms/formulas*)

(*Here things are a bit more complicated. Because Why3 terms encompass both terms and formulas,
  we have to consider some (small) amount of typing. We have several choices:
  1. Give function term_c -> Either term formula (but cannot handle ill-typing e.g. quantify over fmla)
  2. Give 2 functions term_c -> option term and term_c -> option formula
  3. Give 2 functions term_c -> term and term_c -> formula (2 with default values) and prove typing later
  We do the second; later we would want to prove that for well-typed terms, we always get Some
  NOTE: we also send features we don't support (e.g. string constants) to None*)

Definition eval_vsymbol (v: vsymbol) : Syntax.vsymbol :=
  (eval_ident (vs_name v), eval_ty (vs_ty v)).

(*NOTE: not sure semantics of constants is correct: do we need to reason about kind? Only looking 
  at value for now*)

(*I believe: should be (rv_sig r) * 2 ^ (rv_pow2 r) * 5 ^ (rv_pow5 r) (per comments in Number.mli) *)
Definition eval_real_value (r: NumberDefs.real_value) : QArith_base.Q :=
  Qreduction.Qmult'
    (Qreduction.Qmult'
      (QArith_base.inject_Z (rv_sig r))
      (QArith_base.Qpower (QArith_base.inject_Z (rv_pow2 r)) 2))
  (QArith_base.Qpower (QArith_base.inject_Z (rv_pow5 r)) 5).


Definition eval_const (c: constant) : option Syntax.constant :=
  match c with
  | ConstInt i => Some (Syntax.ConstInt (NumberDefs.il_int i))
  | ConstReal r => Some (Syntax.ConstReal (eval_real_value (rl_real r)))
  | ConstStr s => (*don't support yet*) None
  end.


(*Here, we need typing as well*)

(*TODO: move*)
Definition mk_funsym_infer (n: string) (args: list vty) (ret: vty) (is_constr: bool) (num_constrs: nat): funsym.
  refine (Build_funsym (Build_fpsym n (find_args (ret :: args))
    args (find_args_check_args_l _ _ _) (find_args_nodup _)) ret is_constr num_constrs 
      (find_args_check_args_in _ _ _)).
  - intros x Hinx. simpl. right; exact Hinx.
  - simpl. left. reflexivity.
Defined.

Definition mk_predsym_infer (n: string) (args: list vty): predsym.
  refine (Build_predsym (Build_fpsym n (find_args args)
    args (find_args_check_args_l _ _ _) (find_args_nodup _))).
  intros x Hinx; exact Hinx.
Defined.


(*Ignore ls_proj l, we do not have in core
  Assume some well typing: f_is_constr true iff ls_constr <> 0*)
Definition eval_funsym (l: lsymbol) : option funsym :=
  option_map (fun r => 
    mk_funsym_infer (eval_ident (ls_name l)) (map eval_ty (ls_args l)) (eval_ty r)
      (Z.eqb (ls_constr l) 0) (Z.to_nat (ls_constr l))) (ls_value l).

(*Here, only predsym if type is None*)
Definition eval_predsym (l: lsymbol) : option predsym :=
  match ls_value l with
  | None => Some (mk_predsym_infer (eval_ident (ls_name l)) (map eval_ty (ls_args l)))
  | _ => None
  end.

(*TODO: move*)

(*Big difference for terms: core stores explicitly the list of types to substitite for
  the type variables in the symbol. In Why3 this is all implicit. We need an inference
  function to find the list*)

Definition fold_right2_opt {A B C: Type} (f: A -> B -> C -> option C) (base: C) :=
  fix fold (l1: list A) (l2: list B) : option C :=
    match l1, l2 with
    | nil, nil => Some base
    | x1 :: t1, x2 :: t2 => option_bind (fold t1 t2) (f x1 x2) 
    | _, _ => None
    end.

(*gives a map from vars to types such that [v_subst s t1] = t2 if one exists*)
Fixpoint ty_match (t1 t2: vty) (s: amap typevar vty) : option (amap typevar vty) :=
  match t1, t2 with
  | vty_cons ts1 tys1, vty_cons ts2 tys2 =>
    if typesym_eqb ts1 ts2 then
    fold_right2_opt ty_match s tys1 tys2
    else None
  | vty_var n1, _ =>
    (*See if n1 is mapped to t2 (OK) or nothing (add), else None*)
    match amap_lookup s n1 with
    | Some ty3 => if vty_eqb t2 ty3 then Some s else None
    | None => Some (amap_set s n1 t2)
    end
  | _, _ => if vty_eqb t1 t2 then Some s else None
  end.

(*Now use this to infer type map for functions*)
(*Is there a type substitution sigma such that sigma (args) = *)
Definition find_fpsym_map (f: fpsym) (tys: list vty) : option (amap typevar vty) :=
  fold_right2_opt ty_match amap_empty (s_args f) tys.

Definition find_param_vals (params: list typevar) (s: amap typevar vty) : list vty :=
  map (fun p => 
    match amap_lookup s p with
    | Some t => t
    | None => vty_int (*not used so instantiate to anything*)
    end) params.

Definition funpred_ty_list (f: fpsym) (tys: list vty) : option (list vty) :=
  option_map (fun s => find_param_vals (s_params f) s) (find_fpsym_map f tys).

(* 
Definition tfun_infer (f: funsym) (tys: list vty) (tms: list term) : option term :=
  match (find_fpsym_map f tys) with
  | Some s => 
    (*Find values for all type params from s - if not there, not used, so we can
      just assign it int (or whatever)*)
    Some (Tfun f (find_param_vals (s_params f) s) tms)
  | None => None
  end.

Definition tfun_infer_ret (f: funsym) (tys: list vty) (tms: list term) : option (term * vty) :=
  match (find_fpsym_map f (f_ret f :: tys)) (*TODO: is this right?*) with
  | Some s => 
    (*Find values for all type params from s - if not there, not used, so we can
      just assign it int (or whatever)*)
    let tys := (find_param_vals (s_params f) s) in
    Some (Tfun f tys tms, ty_subst (s_params f) tys (f_ret f))
  | None => None
  end. *)

(*NOTE: we ignore the extra metadata: the claimed type, attributes, and location.
  We would use the claimed type for a typing proof*)

Declare Scope option_scope.
Notation "x <- c1 ;; c2" := (@option_bind _ _ c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity) : option_scope.

(*Get types from terms (need for funsyms)*)
Definition term_type (t: term_c) : option vty :=
  option_map eval_ty (t_ty_of t).
Definition pat_type (p: pattern_c) : vty :=
  eval_ty (pat_ty_of p).

Local Open Scope option_scope.

(*Ignore types (mostly) and free vars*)
Fixpoint eval_pat (p: pattern_c) : option Syntax.pattern :=
  match (pat_node_of p) with
  | Pwild => Some (Syntax.Pwild)
  | Pvar v => Some (Syntax.Pvar (eval_vsymbol v))
  | Papp l ps => 
    (*Tricky case - need type substitution*)
    c <- eval_funsym l ;;
    ps' <- fold_list_option (map eval_pat ps) ;;
    (*Also need to get types*)
    let tys := map pat_type ps in
    (*Then check type substitutions*)
    option_map (fun tys1 => Pconstr c tys1 ps') (funpred_ty_list c tys)
  | Por p1 p2 => 
    p1' <- eval_pat p1 ;;
    p2' <- eval_pat p2 ;;
    Some (Syntax.Por p1' p2')
  | Pas p v =>
    p' <- eval_pat p ;;
    Some (Syntax.Pbind p' (eval_vsymbol v))
  end.


Definition eval_binop (b: binop) : Syntax.binop :=
  match b with
  | Tand => Syntax.Tand
  | Tor => Syntax.Tor
  | Timplies => Syntax.Timplies
  | Tiff => Syntax.Tiff
  end.

(*Evaluate terms and formulas*)
Fixpoint eval_term (t: term_c) : option Syntax.term :=
  match (t_node_of t) with
  | Tvar v => Some (Syntax.Tvar (eval_vsymbol v))
  | Tconst c => option_map Syntax.Tconst (eval_const c)
  (*Tapp is tricky*)
  | Tapp l ts => 
    fs <- eval_funsym l ;;
    tms <- fold_list_option (map eval_term ts) ;;
    (*Also need to get types*)
    tys <- fold_list_option (map term_type ts) ;;
    (*Then check type substitutions*)
    option_map (fun tys1 => Tfun fs tys1 tms) (funpred_ty_list fs tys)
  | Tif t1 t2 t3 => 
    t1' <- eval_fmla t1 ;;
    t2' <- eval_term t2 ;;
    t3' <- eval_term t3 ;;
    Some (Syntax.Tif t1' t2' t3')
  | Tlet t1 (v, _, t2) => (*Ignore bind_info, needed for typing*)
    t1' <- eval_term t1 ;;
    t2' <- eval_term t2 ;;
    Some (Syntax.Tlet t1' (eval_vsymbol v) t2')
  | Tcase tm1 pats =>
    tm1' <- eval_term tm1 ;;
    ty1 <- term_type tm1 ;;
    ps1 <- fold_list_option (map (fun x => 
      p <- eval_pat (fst (fst x)) ;;
      t <- eval_term (snd x) ;;
      Some (p, t)
    ) pats) ;;
    Some (Syntax.Tmatch tm1' ty1 ps1)
  | Teps (v, _, t) =>
    f <- eval_fmla t ;;
    Some (Syntax.Teps f (eval_vsymbol v))
  | _ => None
  end
with eval_fmla (t: term_c) : option Syntax.formula :=
  match t_node_of t with
  (*For Fpred, we need to case on equality also, which is not built in to Why3*)
  | Tapp l ts =>
    if lsymbol_eqb l ps_equ then 
    match ts with
    | [t1; t2] =>
      t1' <- eval_term t1 ;;
      t2' <- eval_term t2 ;;
      ty1 <- term_type t1 ;;
      (*NOTE: don't check both types here*)
      Some (Feq ty1 t1' t2')
    | _ => None
    end
    else
    (*Same as funsym*)
    ps <- eval_predsym l ;;
    tms <- fold_list_option (map eval_term ts) ;;
    (*Also need to get types*)
    tys <- fold_list_option (map term_type ts) ;;
    (*Then check type substitutions*)
    option_map (fun tys1 => Fpred ps tys1 tms) (funpred_ty_list ps tys)
  | Tquant q (vs,_, _, f) =>
    f' <- eval_fmla f ;;
    let vs' := map eval_vsymbol vs in
    (*Theirs are iterated, so we use fforalls/fexists*)
    Some match q with
    | Tforall => fforalls vs' f'
    | Texists => fexists vs' f'
    end
  | Tbinop b f1 f2 =>
    f1' <- eval_fmla f1;;
    f2' <- eval_fmla f2;;
    Some (Fbinop (eval_binop b) f1' f2')
  | Tnot f =>
    f' <- eval_fmla f ;;
    Some (Fnot f')
  | Ttrue => Some Ftrue
  | Tfalse => Some Ffalse
  | Tif f1 f2 f3 =>
    f1' <- eval_fmla f1 ;;
    f2' <- eval_fmla f2 ;;
    f3' <- eval_fmla f3 ;;
    Some (Fif f1' f2' f3')
  | Tlet t1 (v, _, f) =>
    t' <- eval_term t1 ;;
    f' <- eval_fmla f ;;
    Some (Flet t' (eval_vsymbol v) f')
  | Tcase tm1 pats =>
    tm1' <- eval_term tm1 ;;
    ty1 <- term_type tm1 ;;
    ps1 <- fold_list_option (map (fun x => 
      p <- eval_pat (fst (fst x)) ;;
      t <- eval_fmla (snd x) ;;
      Some (p, t)
    ) pats) ;;
    Some (Syntax.Fmatch tm1' ty1 ps1)
  |_ => None
  end.

(*NOTE: maybe we will need well-typed assumptions (also because e.g. decl could have
  extra metadata that must be consistent d_news - we might need only 1 identical decl_node in table*)

(*Decls (defs)*)

(*Datatypes*)

Definition eval_constructor (c: constructor) : option funsym :=
  eval_funsym (fst c).

Definition eval_data_decl (d: data_decl) : option alg_datatype :=
  (*constructors must be non-empty*)
  l <- fold_list_option (map eval_constructor (snd d)) ;;
  match l with
  | x :: xs => Some (alg_def (eval_typesym (fst d)) (list_to_ne_list (x :: xs) eq_refl))
  | _ => None
  end.

(*TODO: move*)
Lemma nodupb_nodup {A: Type} eq_dec (l: list A):
  nodupb eq_dec (nodup eq_dec l).
Proof.
  apply (reflect_iff _ _ (nodup_NoDup _ _)), NoDup_nodup.
Qed.

(*To build mut, need to check params of all typesyms in list.
  But we defer the check until typechecking later; for now, just take params of
  first type symbol and check for no duplicates*)
Definition eval_data_decl_list (l: list data_decl) : option Syntax.mut_adt :=
  l' <- fold_list_option (map eval_data_decl l) ;;
  match l' with
  | a :: al => 
    let ts := Types.ts_args (adt_name a) in
    (*Remove duplicates (we can later show that this is unecessary)*)
    Some (mk_mut (a :: al) (nodup typevar_eq_dec ts) (nodupb_nodup _ _))
  | _ => None
  end.

(*TODO: move*)
(*see if lsymbol is funsym or predsym*)
Definition eval_lsymbol_gen (l: lsymbol) : option (funsym + predsym) :=
  if (isSome (ls_value l)) then
    option_map inl (eval_funsym l)
  else option_map inr (eval_predsym l).

(*Concrete functions and predicates*)

(*Here we need both to disambiguate between fun and pred AND to distinguish
  between recursive and nonrecursive*)
(*Additionally, we need to "open" the definition: the definition is really
  forall x, f x = t, when we want parameters x and t*)

(*Recursive functions are encoded as:
  forall x, f x = b
  Predicates are:
  forall x, f x <-> b
  If the function is constant, will just be
  f [] = b or f [] <-> b.
  We evaluate this at the core level
*)

(*Might need many "forall"s*)
Fixpoint extract_foralls (f: formula) : list Syntax.vsymbol * Syntax.formula :=
  match f with
  | Fquant Syntax.Tforall v f => let y := extract_foralls f in
    (v :: (fst y), snd y)
  | _ => (nil, f)
  end.

Definition decode_recfun (f: formula) : option (list Syntax.vsymbol * Syntax.term) :=
  let y := extract_foralls f in
  let vs := fst y in
  let f := snd y in
  (*Now extract the RHS of the equality*)
  match f with
  | Feq _ _ f1 => Some (vs, f1)
  | _ => None
  end.

Definition decode_recpred (f: formula) : option (list Syntax.vsymbol * Syntax.formula) :=
  let y := extract_foralls f in
  let vs := fst y in
  let f := snd y in
  (*Now extract the RHS of the iff*)
  match f with
  | Fbinop Syntax.Tiff _ f1 => Some (vs, f1) (*NOTE: they allow any binop there, probably OK by API construction*)
  | _ => None
  end.


(*Ignore termination indices*)
(*Not sure why lsymbol is there twice, since they are always equal*)
Definition eval_ls_defn (l: ls_defn) : option funpred_def :=
  l' <- eval_lsymbol_gen (fst (fst l)) ;;
  f <- eval_fmla (snd (fst l)) ;;
  match l' with
  | inl fs => 
    (*Function case*)
    y <- decode_recfun f ;;
    let vs := fst y in
    let b := snd y in
    Some (fun_def fs vs b)
  | inr ps =>
    (*Predsym case*)
    y <- decode_recpred f ;;
    let vs := fst y in
    let b := snd y in
    Some (pred_def ps vs b)
  end.

(*Evaluating a logic decl is trivial: we ignore the first function symbol since it must
  be the same (we could check this)*)
Definition eval_logic_decl (l: logic_decl) : option funpred_def :=
  eval_ls_defn (snd l).

(*To check if a function block is recursive, either 1. there is > 1 function in the block 2. the
  symbol appears in the body*)
Definition is_funpred_def_rec (f: funpred_def) : bool :=
  match f with
  | fun_def fs vs b => funsym_in_tm fs b
  | pred_def ps vs b => predsym_in_fmla ps b
  end.

Definition eval_list_logic_decl (l: list logic_decl) : option def :=
  match l with
  | [x] => y <- eval_logic_decl x ;;
    if is_funpred_def_rec y then
    Some (recursive_def [y])
    else Some (nonrec_def y)
  | _ => 
    l <- fold_list_option (map eval_logic_decl l) ;;
    Some (recursive_def l)
  end.

(*Inductive predicates*)

Definition is_ind (i: ind_sign) : bool :=
  match i with
  | Ind => true
  | _ => false
  end.

Definition eval_prsymbol (p: prsymbol) : string :=
  eval_ident (pr_name p).

Definition eval_ind_decl (i: ind_decl) : option indpred_def :=
  p <- eval_predsym (fst i) ;;
  cs <- fold_list_option (map (fun x => 
    f <- eval_fmla (snd x) ;;
    Some (eval_prsymbol (fst x), f)) (snd i) ) ;;
  Some (ind_def p cs).

Definition eval_ind_list (i: ind_list) : option (list indpred_def) :=
  (*We only have semantics for inductive predicates*)
  if is_ind (fst i) then
    fold_list_option (map eval_ind_decl (snd i))
  else None.

(*NOTE: this ONLy evaluates definitions, not hypotheses/goals, we do those later*)
Definition eval_decl_node (d: decl_node) : option def :=
  match d with
  | Dtype t => Some (abs_type (eval_typesym t))
  | Ddata l => m <- eval_data_decl_list l ;; 
      Some (datatype_def m)
  | Dparam l =>
    (*Check to see if funsym or predsym*)
    fp <- eval_lsymbol_gen l ;;
    Some match fp with
    | inl fs => abs_fun fs
    | inr ps => abs_pred ps
    end
  | Dlogic l => eval_list_logic_decl l
  | Dind i => 
    l <- eval_ind_list i ;;
    Some (inductive_def l)
  | Dprop _ => None
  end.

(*NOTE: in tasks, all lemmas are turned into axioms, and there is only 1 goal
  I believe Why3 versions works like:
  1. [flat_tdecl] removes goals, turns lemmas into axioms, imports "use"s
  2. [theory_goals] finds the goals to be proved (not lemmas or goals from clones), user configurable
      to only include some
  3. [split_theory] generates all tasks, with following property: last decl is a Pgoal, there are no
    Plemmas and no other Pgoals  *)

(*split_theory: I believe this is how it works (move):
  maintains task prefix and list of tasks, in each step, appends the tdecls in the current decl
  to the task, then adds a toal if the current task is a lemma or goal, otherwise continues
  so each task has the property that it ends in a goal, has no lemmas (only axioms)
  prefix is original prefix ++ all decls seen so far*)

(*Props - we can ignore lemmas (they are compiled away by [split_theory] into axioms or goals).
  Also we know that there will be only 1 goal in a task, and it should be at the end*)


Definition get_hyp (d: decl_node) : option (string * formula) :=
  match d with
  | Dprop (Paxiom, p, f) =>
    f' <- eval_fmla f ;;
    Some (eval_prsymbol p, f')
  | _ => None
  end.

Definition get_goal (d: decl_node) : option formula :=
  match d with
  | Dprop (Pgoal, p, f) => eval_fmla f
  | _ => None
  end.


(*How to clones work? they are not (directly) compiled in split_theory*)
(*But at some point along the chain, the clones must be resolved - BEFORE running transformations*)

(*Trans.tdecl ignores clones; where are clones considered?*)
(*TODO: should test in Why3 - see what happens if we clone then run elim_def*)
(*NOTE: move
  [do_theory] in why3prove.ml calls [split_theory], then runs [do_tasks] which
  applies transformations, then [do_task] sends to prover, just applies it.
  Not sure where clones are desugared, but for now we assume that all clones are gone*)

Definition eval_decl (d: decl) : option def := eval_decl_node (d_node d).
Definition eval_decl_hyp (d: decl) : option (string * formula) := get_hyp (d_node d).
Definition eval_decl_goal (d: decl) : option formula := get_goal (d_node d).

(*tdecl*)
Definition eval_tdecl_node_aux {A} (f: decl -> option A) (t: tdecl_node) : option A :=
  match t with
  | Decl d => f d
  | _ => None
  end.

Definition eval_tdecl (t: tdecl_c) := eval_tdecl_node_aux eval_decl (td_node_of t).
Definition eval_tdecl_hyp (t: tdecl_c) := eval_tdecl_node_aux eval_decl_hyp (td_node_of t).
Definition eval_tdecl_goal (t: tdecl_c) := eval_tdecl_node_aux eval_decl_goal (td_node_of t).

(*Finally, task*)

(*task_hd is not quite a list, but it is close. 
  We need 3 parts: we get gamma, delta, and the goal separately*)
Fixpoint eval_task_gen {A} (f: tdecl_c -> option A) (t : task_hd) : option (list A) :=
  t' <- f (task_decl t) ;;
  match (task_prev t) with
  | None => Some [t']
  | Some tsk => 
    l <- eval_task_gen f tsk;;
    Some (t' :: l)
  end.

Definition eval_task_ctx (t: task_hd) : option context :=
  eval_task_gen eval_tdecl t.
Definition eval_task_hyps (t: task_hd) : option (list (string * formula)) :=
  eval_task_gen eval_tdecl_hyp t.
(*NOTE: for goal, we assume it is at the end*)
Definition eval_task_goal (t: task_hd) : option formula :=
  eval_tdecl_goal (task_decl t).

Definition eval_task (t: task) : option Task.task :=
  gamma <- option_bind t eval_task_ctx ;;
  delta <- option_bind t eval_task_hyps ;;
  goal <- option_bind t eval_task_goal ;;
  Some (gamma, delta, goal).

(*And now a definition of validity: Why3 task t is valid if t ==> t' and t' is sound*)
Definition valid_task (t: task) : Prop :=
  exists t', eval_task t = Some t' /\ Task.task_valid t'.

(*NOTE: eventually I should give a type system for the augmented terms and prove this*)
Definition typed_task (t: task) : Prop :=
  exists t', eval_task t = Some t' /\ Task.task_typed t'.

End Eval.

(*Now define relations: when is a Why3 term related to a core term?
  Not just eval, we want alpha equivalence, and we need to push through defs*)
(*NOTE: there are several ways we could generalize this, if needed
  1. In funpred def, could allow variables to change as long as alpha equivalent under corresponding vars
  2. Could allow renaming of fun/pred/type syms (would likely need for eliminate_algebraic)
  3. Could allow renaming of type symbols (don't think needed) *)
Section Relations.

Definition term_related (t1: term_c) (t2: Syntax.term) : Prop :=
  exists tm, eval_term t1 = Some tm /\ a_equiv_t tm t2.
Definition fmla_related (f1: term_c) (f2: Syntax.formula) : Prop :=
  exists f, eval_fmla f1 = Some f /\ a_equiv_f f f2.


(*Now we "lift" alpha equivalence to defs. This is all in core and should be moved*)
Definition a_equiv_funpred_def (fd1 fd2: funpred_def) : bool :=
  match fd1, fd2 with
  | fun_def f1 vs1 t1, fun_def f2 vs2 t2 =>
    (*NOTE: for now, just require variables to be the same and terms to be alpha equivalent.
      Eventually, if needed, could say that forall x, t1 is alpha equiv to forall y, t2.
      However, I don't think that we ever actually alpha convert these variables, so may not
      be necessary*)
    (*It is NOT enough to just say that the terms are alpha equivalent, even if we assume the
      variable lists are equal. The problem is termination: one variable could be overwritten
      and not the other. While eventually using this information would violate alpha equivalence,
      proving this is very tricky, and it is easier to just assume alpha equivalence under
      the map mapping the corresponding variables *)

    funsym_eqb f1 f2 && (length vs1 =? length vs2) && list_eqb vty_eqb (map snd vs1) (map snd vs2) &&
    nodupb string_dec (map fst vs1) && nodupb string_dec (map fst vs2) &&
    alpha_equiv_t (list_to_amap (combine vs1 vs2)) (list_to_amap (combine vs2 vs1)) t1 t2
 (* list_eqb Syntax.vsymbol_eqb vs1 vs2 && a_equiv_t t1 t2 *)
  | pred_def p1 vs1 f1, pred_def p2 vs2 f2 =>
    predsym_eqb p1 p2 &&  (length vs1 =? length vs2) && list_eqb vty_eqb (map snd vs1) (map snd vs2) &&
    nodupb string_dec (map fst vs1) && nodupb string_dec (map fst vs2) &&
    alpha_equiv_f (list_to_amap (combine vs1 vs2)) (list_to_amap (combine vs2 vs1)) f1 f2
(* list_eqb Syntax.vsymbol_eqb vs1 vs2 && a_equiv_f f1 f2 *)
  | _, _ => false
  end.

(*Inductive predicate*)

Definition a_equiv_indpred_def (i1 i2: indpred_def) : bool :=
  match i1, i2 with
  | ind_def p1 fs1, ind_def p2 fs2 =>
    (*don't care about names*)
    predsym_eqb p1 p2 && (length fs1 =? length fs2) && all2 a_equiv_f (map snd fs1) (map snd fs2)
  end.


(*NOTE: eventually, might need expanded version that has map between fun/pred sym names.
  But for now just assume equiv*)
Definition a_equiv_def (d1 d2: def) : bool :=
  match d1, d2 with
  | datatype_def m1, datatype_def m2 => Syntax.mut_adt_eqb m1 m2
  | recursive_def fs1, recursive_def fs2 => (length fs1 =? length fs2) && all2 a_equiv_funpred_def fs1 fs2
  | inductive_def il1, inductive_def il2 => (length il1 =? length il2) && all2 a_equiv_indpred_def il1 il2
  | nonrec_def f1, nonrec_def f2 => a_equiv_funpred_def f1 f2
  | abs_type ts1, abs_type ts2 => typesym_eqb ts1 ts2
  | abs_fun f1, abs_fun f2 => funsym_eqb f1 f2
  | abs_pred p1, abs_pred p2 => predsym_eqb p1 p2
  | _, _ => false
  end.

Definition a_equiv_ctx (g1 g2: context) : bool :=
  (length g1 =? length g2) && all2 a_equiv_def g1 g2.

Definition a_equiv_task (t1 t2: Task.task) : bool :=
  a_equiv_ctx (task_gamma t1) (task_gamma t2) &&
  (length (task_delta t1) =? length (task_delta t2)) &&
  all2 a_equiv_f (map snd (task_delta t1)) (map snd (task_delta t2)) &&
  a_equiv_f (Task.task_goal t1) (Task.task_goal t2).

Definition task_related (t1: task) (t2: Task.task) : Prop :=
  exists t, eval_task t1 = Some t /\ a_equiv_task t t2.

End Relations.

