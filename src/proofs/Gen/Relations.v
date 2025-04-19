From Proofs Require Import Task AssocList Alpha.
Require Import TyDefs TyFuncs NumberDefs TermDefs TermFuncs DeclDefs TheoryDefs TaskDefs TransDefs.
Require Import VsymCount.

(*TODO: BAD - for under_str*)
From Proofs Require Import eliminate_algebraic eliminate_algebraic_interp.

(*Define "eval" function: takes augmented type/term/etc, produces core type/term/etc*)
Section Eval.

(*Idents*)

(*An ident is evaluated to its name followed by its id (which is always positive)*)
(*Doesn't quite work - need underscore then optional minus because for proofs we need to assume it could
  be negative*)

Definition z_to_string (z: Z) : string :=
  if (Z.ltb z 0) then "n" ++ GenElts.nat_to_string (Z.to_nat (Z.opp z)) else
    GenElts.nat_to_string (Z.to_nat z).

Definition eval_ident (i: ident) : string :=
  (id_string i) ++ under_str ++ (z_to_string (id_tag i)) .


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

(*NOTE: vsymbol not compositional because we need it to be injective*)

(*A super bad positive to string function - but OK for us, all we need is injectivity*)
Fixpoint pos_to_string (p: positive) : string :=
  match p with
  | xI p => "1" ++ pos_to_string p
  | xO p => "0" ++ pos_to_string p
  | xH => "1"
  end.

Definition eval_vsymbol (v: vsymbol) : Syntax.vsymbol :=
  (pos_to_string (countable.encode v), eval_ty (vs_ty v)).

(* Definition eval_vsymbol (v: vsymbol) : Syntax.vsymbol :=
  (eval_ident (vs_name v), eval_ty (vs_ty v)). *)

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

(*NOTE: this ONLy evaluates definitions, not hypotheses/goals, we do those later*)
(*NOTE: options are not enough: we need to distinguish bewteen ill-typed defs and non-defs*)

(*The final +unit represents goals*)
Definition eval_decl_node (d: decl_node) : option def + (option (string * formula) + unit) :=
  match d with
  | Dtype t => inl (Some (abs_type (eval_typesym t)))
  | Ddata l => inl (m <- eval_data_decl_list l ;; 
      Some (datatype_def m))
  | Dparam l =>
    (*Check to see if funsym or predsym*)
    inl (fp <- eval_lsymbol_gen l ;;
    Some match fp with
    | inl fs => abs_fun fs
    | inr ps => abs_pred ps
    end)
  | Dlogic l => inl (eval_list_logic_decl l)
  | Dind i => 
    inl (l <- eval_ind_list i ;;
    Some (inductive_def l))
  | Dprop (Paxiom, p, f) =>
    inr (inl (f' <- eval_fmla f ;;
    Some (eval_prsymbol p, f')))
  | Dprop _ => inr (inr tt)
  end.

(* 

Definition get_hyp (d: decl_node) : option (string * formula) :=
  match d with
  | Dprop (Paxiom, p, f) =>
    f' <- eval_fmla f ;;
    Some (eval_prsymbol p, f')
  | _ => None
  end. *)

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

Definition eval_decl (d: decl):  option def + (option (string * formula) + unit) :=
  eval_decl_node (d_node d).
Definition eval_decl_goal (d: decl) : option formula := get_goal (d_node d).

(* Definition eval_decl (d: decl) : option def := eval_decl_node (d_node d).
Definition eval_decl_hyp (d: decl) : option (string * formula) := get_hyp (d_node d).
Definition eval_decl_goal (d: decl) : option formula := get_goal (d_node d). *)

(*tdecl*)
Definition eval_tdecl_node_aux {A} (f: decl -> A) (t: tdecl_node) : option A :=
  match t with
  | Decl d => Some (f d)
  | _ => None
  end.

Definition eval_tdecl (t: tdecl_c) := eval_tdecl_node_aux eval_decl (td_node_of t).
(* Definition eval_tdecl_hyp (t: tdecl_c) := eval_tdecl_node_aux eval_decl_hyp (td_node_of t). *)
Definition eval_tdecl_goal (t: tdecl_c) := option_collapse (eval_tdecl_node_aux eval_decl_goal (td_node_of t)).

(*Finally, task*)

(*task_hd is not quite a list, but it is close. First, make it into a list*)

(*Dont love [task_list] maybe redefine, maybe it is more efficient. But we don't care
  about efficiency here*)

Fixpoint task_hd_decls (t: task_hd) : list tdecl_c :=
  (task_decl t) :: 
  match (task_prev t) with
  | Some tsk => task_hd_decls tsk
  | None => nil
  end.


Definition get_inl {A B: Type} (l: list (A + B)) : list A :=
  omap (fun x => match x with | inl y => Some y | _ => None end) l.
Definition get_inr {A B C: Type} (l: list (A + (B + C))) : list B :=
  omap (fun x => match x with | inr (inl y) => Some y | _ => None end) l.

(*To evaluate the context, we need all of the inl elements to be Some*)
(*NOTE: ignoring meta (use/clone should already be compiled), not failnig on meta*)
Definition eval_task_ctx (t: task_hd) : option context :=
  let l := omap eval_tdecl  (task_hd_decls t) in 
  (*only consider hyps, make sure all well-typed*)
  fold_list_option (get_inl l).

Definition eval_task_hyps (t: task_hd) : option (list (string * formula)) :=
  let l := omap eval_tdecl  (task_hd_decls t) in 
  fold_list_option (get_inr l).

(* 
Definition eval_task_gen {A B} f (t : task_hd) : option (list A) :=
  let l := omap eval_tdecl (task_hd_decls t) in
  (*Now we need all defs to be some*)
  all_some f l.

Definition eval_task_gen {A} (f: tdecl_c -> option A) (t : task_hd) : option (list A) :=
  omap f (task_hd_decls t).

  We need 3 parts: we get gamma, delta, and the goal separately
Fixpoint eval_task_gen {A} (f: tdecl_c -> option A) (t : task_hd) : option (list A) :=
  (*NOT bind: basically omap - we just want to skip None entries*)
  let t' := f (task_decl t) in
  match (task_prev t) with
  | None => option_map (fun x => [x]) t'
  | Some tsk => 
    let l := eval_task_gen f tsk in
    match t' with
    | None => l
    | Some t' =>
      match l with
      | None => Some [t']
      | Some l => Some (t' :: l)
      end
    end
  end.

Definition eval_task_ctx (t: task_hd) : option context :=
  eval_task_gen eval_tdecl t.
Definition eval_task_hyps (t: task_hd) : option (list (string * formula)) :=
  eval_task_gen eval_tdecl_hyp t. *)
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
(*A little trick: we cannot assume nodups, or else we lose reflexivity.
  But we do need for typing. Solution: it is enough that either both are nodups or neither is,
  since in typing we assume that one is*)
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
    (Bool.eqb (nodupb string_dec (map fst vs1)) (nodupb string_dec (map fst vs2))) &&
    alpha_equiv_t (list_to_amap (combine vs1 vs2)) (list_to_amap (combine vs2 vs1)) t1 t2
 (* list_eqb Syntax.vsymbol_eqb vs1 vs2 && a_equiv_t t1 t2 *)
  | pred_def p1 vs1 f1, pred_def p2 vs2 f2 =>
    predsym_eqb p1 p2 &&  (length vs1 =? length vs2) && list_eqb vty_eqb (map snd vs1) (map snd vs2) &&
    (Bool.eqb (nodupb string_dec (map fst vs1)) (nodupb string_dec (map fst vs2)) )&&
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

(*Some syntactic results about evaluation and relations (RelationProofs.v has semantic results)*)


(*[eval_task_goal] is annoying. This lets us rewrite it in terms of [find_goal] and relate the formulas*)
Lemma eval_task_find_goal (tsk: task_hd) (f: formula):
  eval_task_goal tsk = Some f <->
  exists f1 pr, find_goal (Some tsk) = Some (pr, f1) /\ eval_fmla f1 = Some f.
Proof.
  unfold eval_task_goal, eval_tdecl_goal, eval_tdecl_node_aux, eval_decl_goal.
  unfold find_goal. simpl.
  destruct (td_node_of (task_decl tsk)) as [d | | |] eqn : Htd; try solve[split; intros; destruct_all; discriminate].
  unfold get_goal.
  destruct (d_node d) as [| | | | | [[k pr] f1]] eqn : Hd; try solve[split; intros; destruct_all; discriminate].
  simpl in *. destruct k; try solve[split; intros; destruct_all; discriminate].
  destruct (eval_fmla f1) as [f2|] eqn : Heval.
  - split.
    + intros Hsome; inversion Hsome; subst. exists f1. exists pr. auto.
    + intros [f2' [pr1 [Hsome Heval']]]. inversion Hsome; subst; auto. rewrite Heval in Heval'.
      inversion Heval'; subst; auto.
  - split; try discriminate. 
    intros [f2' [pr1 [Hsome Heval']]]. inversion Hsome; subst; auto.  rewrite Heval in Heval'. discriminate.
Qed.

(*Now prove related by parts*)
Section ProveRelated.

Import Task.

Lemma fmla_related_fif t1 t2 t3 e1 e2 e3:
  fmla_related t1 e1 ->
  fmla_related t2 e2 ->
  fmla_related t3 e3 ->
  fmla_related (t_if1 t1 t2 t3) (Fif e1 e2 e3).
Proof.
  intros Hrel1 Hrel2 Hrel3.
  unfold fmla_related in *.
  simpl. destruct Hrel1 as [f1 [He1 Ha1]].
  destruct Hrel2 as [f2 [He2 Ha2]].
  destruct Hrel3 as [f3 [He3 Ha3]].
  exists (Fif f1 f2 f3). rewrite He1, He2, He3. simpl.
  split; auto.
  (*TODO: prove separately*)
  unfold a_equiv_f. simpl.
  bool_to_prop; split_all; auto.
Qed.

Lemma term_related_tif t1 t2 t3 e1 e2 e3:
  fmla_related t1 e1 ->
  term_related t2 e2 ->
  term_related t3 e3 ->
  term_related (t_if1 t1 t2 t3) (Tif e1 e2 e3).
Proof.
  intros Hrel1 Hrel2 Hrel3.
  unfold fmla_related, term_related in *.
  simpl. destruct Hrel1 as [f1 [He1 Ha1]].
  destruct Hrel2 as [f2 [He2 Ha2]].
  destruct Hrel3 as [f3 [He3 Ha3]].
  exists (Tif f1 f2 f3). rewrite He1, He2, He3. simpl.
  split; auto.
  unfold a_equiv_t. simpl.
  bool_to_prop; split_all; auto.
Qed.

End ProveRelated.

Require Import TermTactics.
Import Task.



(*Proofs about [eval_*] and preservation under t_similar and t_attr_copy*)

Lemma eval_term_rewrite t:
  eval_term t = match t_node_of t with
  | TermDefs.Tvar v => Some (Tvar (eval_vsymbol v))
  | TermDefs.Tconst c => option_map Tconst (eval_const c)
  | Tapp l ts =>
      option_bind (eval_funsym l)
        (fun fs : funsym =>
         option_bind (fold_list_option (map eval_term ts))
           (fun tms : list term =>
            option_bind (fold_list_option (map term_type ts))
              (fun tys : list vty =>
               option_map (fun tys1 : list vty => Tfun fs tys1 tms) (funpred_ty_list fs tys))))
  | TermDefs.Tif t1 t2 t3 =>
      option_bind (eval_fmla t1)
        (fun t1' : formula =>
         option_bind (eval_term t2)
           (fun t2' : term => option_bind (eval_term t3) (fun t3' : term => Some (Tif t1' t2' t3'))))
  | TermDefs.Tlet t1 (v, _, t2) =>
      option_bind (eval_term t1)
        (fun t1' : term =>
         option_bind (eval_term t2) (fun t2' : term => Some (Tlet t1' (eval_vsymbol v) t2')))
  | Tcase tm1 pats =>
      option_bind (eval_term tm1)
        (fun tm1' : term =>
         option_bind (term_type tm1)
           (fun ty1 : vty =>
            option_bind
              (fold_list_option
                 (map
                    (fun x : pattern_c * bind_info * term_c =>
                     option_bind (eval_pat (fst (fst x)))
                       (fun p : pattern =>
                        option_bind (eval_term (snd x)) (fun t0 : term => Some (p, t0)))) pats))
              (fun ps1 : list (pattern * term) => Some (Tmatch tm1' ty1 ps1))))
  | TermDefs.Teps (v, _, t0) =>
      option_bind (eval_fmla t0) (fun f : formula => Some (Teps f (eval_vsymbol v)))
  | _ => None
  end.
Proof. destruct t;
reflexivity.
Qed.

Lemma eval_fmla_rewrite t:
  eval_fmla t = match t_node_of t with
  | Tapp l ts =>
      if lsymbol_eqb l ps_equ
      then
       match ts with
       | [] => None
       | [t1] => None
       | [t1; t2] =>
           option_bind (eval_term t1)
             (fun t1' : term =>
              option_bind (eval_term t2)
                (fun t2' : term => option_bind (term_type t1) (fun ty1 : vty => Some (Feq ty1 t1' t2'))))
       | t1 :: t2 :: _ :: _ => None
       end
      else
       option_bind (eval_predsym l)
         (fun ps : predsym =>
          option_bind (fold_list_option (map eval_term ts))
            (fun tms : list term =>
             option_bind (fold_list_option (map term_type ts))
               (fun tys : list vty =>
                option_map (fun tys1 : list vty => Fpred ps tys1 tms) (funpred_ty_list ps tys))))
  | TermDefs.Tif f1 f2 f3 =>
      option_bind (eval_fmla f1)
        (fun f1' : formula =>
         option_bind (eval_fmla f2)
           (fun f2' : formula =>
            option_bind (eval_fmla f3) (fun f3' : formula => Some (Fif f1' f2' f3'))))
  | TermDefs.Tlet t1 (v, _, f) =>
      option_bind (eval_term t1)
        (fun t' : term =>
         option_bind (eval_fmla f) (fun f' : formula => Some (Flet t' (eval_vsymbol v) f')))
  | Tcase tm1 pats =>
      option_bind (eval_term tm1)
        (fun tm1' : term =>
         option_bind (term_type tm1)
           (fun ty1 : vty =>
            option_bind
              (fold_list_option
                 (map
                    (fun x : pattern_c * bind_info * term_c =>
                     option_bind (eval_pat (fst (fst x)))
                       (fun p : pattern =>
                        option_bind (eval_fmla (snd x)) (fun t0 : formula => Some (p, t0)))) pats))
              (fun ps1 : list (pattern * formula) => Some (Fmatch tm1' ty1 ps1))))
  | Tquant q (vs, _, _, f) =>
      option_bind (eval_fmla f)
        (fun f' : formula =>
         let vs' := map eval_vsymbol vs in
         Some
           match q with
           | TermDefs.Tforall => fforalls vs' f'
           | TermDefs.Texists => fexists vs' f'
           end)
  | Tbinop b f1 f2 =>
      option_bind (eval_fmla f1)
        (fun f1' : formula =>
         option_bind (eval_fmla f2) (fun f2' : formula => Some (Fbinop (eval_binop b) f1' f2')))
  | Tnot f => option_bind (eval_fmla f) (fun f' : formula => Some (Fnot f'))
  | Ttrue => Some Ftrue
  | Tfalse => Some Ffalse
  | _ => None
  end.
Proof. destruct t; auto. Qed.

Lemma lex_comp_zero i1 i2:
  IntFuncs.lex_comp i1 i2 = CoqInt.zero ->
  i1 = CoqInt.zero /\ i2 = CoqInt.zero.
Proof.
  unfold IntFuncs.lex_comp.
  unfold CoqInt.is_zero. destruct (CoqInt.int_eqb i1 CoqInt.zero) eqn : Heq.
  - intros Hi2. apply CoqInt.int_eqb_eq in Heq. auto.
  - intros Hi1. subst. discriminate.
Qed.

(*TODO: move??*)
Lemma coqint_compare_zero z1 z2:
  CoqBigInt.compare z1 z2 = CoqInt.zero ->
  z1 = z2.
Proof.
  (*TODO: bad*) Transparent CoqBigInt.compare. unfold CoqBigInt.compare, CoqInt.compare_to_int.
  destruct (Z.compare z1 z2) eqn : Hcomp; try discriminate.
  apply Z.compare_eq_iff in Hcomp. subst; auto.
  Opaque CoqBigInt.compare.
Qed.

Lemma const_compare_eval c1 c2:
  compare_const_aux true c1 c2 = CoqInt.zero ->
  eval_const c1 = eval_const c2.
Proof.
  unfold compare_const_aux, eval_const.
  destruct c1 as [i1 | r1 | s1]; destruct c2 as [i2 | r2 | s2]; simpl; try discriminate.
  - destruct i1 as [k1 i1]; destruct i2 as [k2 i2]; simpl in *.
    intros Hz. apply lex_comp_zero in Hz. destruct Hz as [Hc1 Hc2].
    apply coqint_compare_zero in Hc2. subst; auto.
  - (*reals*) intros Hz. destruct r1 as [k1 r1]; destruct r2 as [k2 r2]; simpl in *. unfold eval_real_value.
    destruct r1 as [s1 t1 f1]; destruct r2 as [s2 t2 f2]; simpl in *.
    apply lex_comp_zero in Hz. destruct Hz as [Hz1 Hz].
    apply lex_comp_zero in Hz. destruct Hz as [Hz2 Hz].
    apply lex_comp_zero in Hz. destruct Hz as [Hz3 Hz].
    apply coqint_compare_zero in Hz2, Hz3, Hz. subst; auto.
  - (*string*)  unfold IntFuncs.string_compare, CoqInt.compare_to_int.
    destruct (compare s1 s2) eqn : Hcomp; try discriminate. auto.
Qed.
   
Lemma t_similar_eval t s:
  t_similar t s ->
  eval_term t = eval_term s.
Proof.
  unfold t_similar. rewrite andb_true.
  intros [Hoeq Hsim].
  rewrite !eval_term_rewrite.
  get_fast_eq.
  destruct_term_node t; destruct_term_node s; try discriminate; auto; solve_similar.
  apply CoqInt.int_eqb_eq, const_compare_eval in Hsim. f_equal. auto.
Qed.
  
Lemma t_attr_copy_eval t s:
  eval_term (t_attr_copy t s) = eval_term s.
Proof.
  unfold t_attr_copy. destruct (_ && _) eqn : Hsim.
  - apply t_similar_eval. bool_hyps; auto.
  - rewrite !eval_term_rewrite; simpl; auto.
Qed. 

Lemma t_similar_eval_fmla t s:
  t_similar t s ->
  eval_fmla t = eval_fmla s.
Proof.
  unfold t_similar. rewrite andb_true.
  intros [Hoeq Hsim].
  rewrite !eval_fmla_rewrite.
  get_fast_eq.
  destruct_term_node t; destruct_term_node s; try discriminate; auto; solve_similar.
Qed.
  
Lemma t_attr_copy_eval_fmla t s:
  eval_fmla (t_attr_copy t s) = eval_fmla s.
Proof.
  unfold t_attr_copy. destruct (_ && _) eqn : Hsim.
  - apply t_similar_eval_fmla. bool_hyps; auto.
  - rewrite !eval_fmla_rewrite; simpl; auto.
Qed. 
