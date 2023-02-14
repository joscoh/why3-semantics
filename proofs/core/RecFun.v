(*Recursive Functions*)
Require Import Syntax.
Require Import Types.
Require Import Typing.
Require Import Semantics.

(*First, define syntactic restriction on functions*)

(*For our purposes here, a function declaration is a tuple
  consisting of the name, arguments, index of the argument that
  is decreasing, and body*)
Record fn := mk_fn {fn_name: funsym; fn_args: list vsymbol;
  fn_idx : nat; fn_idx_in: fn_idx <? length fn_args}.
Record pn := mk_pn {pn_name: predsym; pn_args: list vsymbol;
  pn_idx: nat; pn_idx_in: pn_idx <? length pn_args}.

(*TODO: combine with [predsym_in]*)
Fixpoint funsym_in_tm (f: funsym) (t: term) : bool :=
  match t with
  | Tfun fs _ tms => funsym_eq_dec f fs || existsb (funsym_in_tm f) tms
  | Tlet t1 _ t2 => funsym_in_tm f t1 || funsym_in_tm f t2
  | Tif f1 t1 t2 => funsym_in_fmla f f1 || funsym_in_tm f t1 ||
    funsym_in_tm f t2
  | Tmatch t1 _ ps => funsym_in_tm f t1 ||
    existsb (fun x => funsym_in_tm f (snd x)) ps
  | Teps f1 _ => funsym_in_fmla f f1
  | _ => false
  end
  with funsym_in_fmla (f: funsym) (f1: formula) : bool :=
  match f1 with
  | Fpred _ _ tms => existsb (funsym_in_tm f) tms
  | Feq _ t1 t2 => funsym_in_tm f t1 || funsym_in_tm f t2
  | Fbinop _ fm1 fm2 => funsym_in_fmla f fm1 || funsym_in_fmla f fm2
  | Fquant _ _ f' | Fnot f' => funsym_in_fmla f f'
  | Flet t _ f' => funsym_in_tm f t || funsym_in_fmla f f'
  | Fif fm1 fm2 fm3 => funsym_in_fmla f fm1 || funsym_in_fmla f fm2 ||
    funsym_in_fmla f fm3
  | Fmatch t _ ps => funsym_in_tm f t ||
    existsb (fun x => funsym_in_fmla f (snd x)) ps
  | _ => false
  end.

Fixpoint test {A: Type} (l: list A) : list A :=
  match l with
  | nil => nil
  | x :: t =>
    match t with
    | nil => nil
    | y :: v => test v
    end
  end.

Fixpoint test2 {A: Type} (l: list A) : list A :=
  match (length l =? 8) with
  | true => nil
  | false => match l with
                | nil => nil
                | x :: t => test2 t
                end
  end.

Fixpoint testpred {A: Type} (l1 l2: list A) : Prop :=
  forall x,
    match l1 with
    | nil => False
    | _ :: t => testpred t x
    end.

(*PROBLEM! My syntax is not correct - functions and predicates
  can be recursive together - so we need something like:
  list (Either fn pn)
  or maybe nicer - list of fs followed by list of ps
  (we can always reorder)*)

(*The list of vsymbols denotes all variables we "know" to be
  smaller than the argument, which is the second argument to the
  relation*)
Inductive decrease_fun (fs: list fn) (ps: list pn) : 
  list vsymbol -> vsymbol -> term -> Prop :=
  (*First, the recursive function call case*)
  | Dec_fun_in: forall (small: list vsymbol) (hd: vsymbol) 
    (f: funsym) (f_decl: fn) (l: list vty) (ts: list term),
    In f_decl fs ->
    f = fn_name f_decl ->
    (*The decreasing argument must be in our list of decreasing terms*)
    In (nth (fn_idx f_decl) (fn_args f_decl) vs_d) small ->
    (*None of [fs] of [ps] appear in the terms*) 
    (*TODO: will likely need this to show we can ignore function binding in interp for recursive cases*)
    (forall f t, In f fs -> In t ts -> negb (funsym_in_tm (fn_name f) t)) ->
    (forall p t, In p ps -> In t ts -> negb (predsym_in_term (pn_name p) t)) ->
    (*Then this recursive call is valid*)
    decrease_fun fs ps small hd (Tfun f l ts)
  (*Other function call*)
  | Dec_fun_notin: forall (small: list vsymbol) (hd: vsymbol) 
    (f: funsym) (l: list vty) (ts: list term),
    ~ In f (map fn_name fs) ->
    (*In this case, just recursive*)
    Forall (decrease_fun fs ps small hd) ts ->
    decrease_fun fs ps small hd (Tfun f l ts)
  (*Pattern match on var - this is how we add new, smaller variables*)
  | Dec_tmatch: forall (small: list vsymbol) (hd: vsymbol)
    (mvar: vsymbol) (v: vty) (pats: list (pattern * term)),
    (*TODO: can we only match on a variable?*)
    mvar = hd \/ In mvar small ->
    (*TODO: don't allow repeated matches on same variable*)
    Forall (fun x => decrease_fun fs ps (pat_fv (fst x) ++ small) mvar (snd x)) pats ->
    decrease_fun fs ps small hd (Tmatch (Tvar mvar) v pats) 
  (*Other pattern match is recursive case*)
  | Dec_tmatch_rec: forall (small: list vsymbol) (hd: vsymbol)
    (tm: term) (v: vty) (pats: list (pattern * term)),
    ~(exists var, tm = Tvar var /\ (var = hd \/ In var small)) ->
    Forall (fun x => decrease_fun fs ps small hd (snd x)) pats ->
    decrease_fun fs ps small hd (Tmatch tm v pats)
  (*Now the easy cases: Constants, Variables always decreasing*)
  | Dec_var: forall (small : list vsymbol) (hd: vsymbol) (v: vsymbol),
    decrease_fun fs ps small hd (Tvar v)
  | Dec_const: forall (small : list vsymbol) (hd: vsymbol) (c: constant),
    decrease_fun fs ps small hd (Tconst c)
  (*Recursive cases: let, if, eps*)
  | Dec_tlet: forall (small: list vsymbol) (hd: vsymbol) (t1: term)
    (v: vsymbol) (t2: term),
    decrease_fun fs ps small hd t1 ->
    decrease_fun fs ps small hd t2 ->
    decrease_fun fs ps small hd (Tlet t1 v t2)
  | Dec_tif: forall (small: list vsymbol) (hd: vsymbol) (f1: formula)
    (t1 t2: term),
    decrease_pred fs ps small hd f1 ->
    decrease_fun fs ps small hd t1 ->
    decrease_fun fs ps small hd t2 ->
    decrease_fun fs ps small hd (Tif f1 t1 t2)
  | Dec_eps: forall (small: list vsymbol) (hd: vsymbol) (f: formula)
    (v: vsymbol),
    decrease_pred fs ps small hd f ->
    decrease_fun fs ps small hd (Teps f v)
(*This is very similar*)
with decrease_pred (fs: list fn) (ps: list pn) : 
  list vsymbol -> vsymbol -> formula -> Prop :=
  (*First, the recursive predicate call case*)
  | Dec_pred_in: forall (small: list vsymbol) (hd: vsymbol) 
    (p: predsym) (p_decl: pn) (l: list vty) (ts: list term),
    In p_decl ps ->
    p = pn_name p_decl ->
    (*The decreasing argument must be in our list of decreasing terms*)
    In (nth (pn_idx p_decl) (pn_args p_decl) vs_d) small ->
    (*None of [fs] or[ps] appear in the terms*) 
    (*TODO: will likely need this to show we can ignore function binding in interp for recursive cases*)
    (forall f t, In f fs -> In t ts -> negb (funsym_in_tm (fn_name f) t)) ->
    (forall p t, In p ps -> In t ts -> negb (predsym_in_term (pn_name p) t)) ->
    (*Then this recursive call is valid*)
    decrease_pred fs ps small hd (Fpred p l ts)
  (*Other predicate call*)
  | Dec_pred_notin: forall (small: list vsymbol) (hd: vsymbol) 
    (p: predsym) (l: list vty) (ts: list term),
    ~ In p (map pn_name ps) ->
    (*In this case, just recursive*)
    Forall (decrease_fun fs ps small hd) ts ->
    decrease_pred fs ps small hd (Fpred p l ts)
  (*Pattern match on var - this is how we add new, smaller variables*)
  | Dec_fmatch: forall (small: list vsymbol) (hd: vsymbol)
    (mvar: vsymbol) (v: vty) (pats: list (pattern * formula)),
    (*TODO: can we only match on a variable?*)
    mvar = hd \/ In mvar small ->
    (*TODO: don't allow repeated matches on same variable*)
    Forall (fun x => decrease_pred fs ps (pat_fv (fst x) ++ small) mvar (snd x)) pats ->
    decrease_pred fs ps small hd (Fmatch (Tvar mvar) v pats) 
  (*Other pattern match is recursive case*)
  | Dec_fmatch_rec: forall (small: list vsymbol) (hd: vsymbol)
    (tm: term) (v: vty) (pats: list (pattern * formula)),
    ~(exists var, tm = Tvar var /\ (var = hd \/ In var small)) ->
    Forall (fun x => decrease_pred fs ps small hd (snd x)) pats ->
    decrease_pred fs ps small hd (Fmatch tm v pats)
  (*Easy cases: true, false*)
  | Dec_true: forall (small: list vsymbol) (hd: vsymbol),
    decrease_pred fs ps small hd Ftrue
  | Dec_false: forall (small: list vsymbol) (hd: vsymbol),
    decrease_pred fs ps small hd Ffalse
  (*Recursive cases: quantifier, eq, binop, let, if*)
  | Dec_quant: forall (small: list vsymbol) (hd: vsymbol)
    (q: quant) (v: vsymbol) (f: formula),
    decrease_pred fs ps small hd f ->
    decrease_pred fs ps small hd (Fquant q v f)
  | Dec_eq: forall (small: list vsymbol) (hd: vsymbol)
    (ty: vty) (t1 t2: term),
    decrease_fun fs ps small hd t1 ->
    decrease_fun fs ps small hd t2 ->
    decrease_pred fs ps small hd (Feq ty t1 t2)
  | Dec_binop: forall (small: list vsymbol) (hd: vsymbol)
    (b: binop) (f1 f2: formula),
    decrease_pred fs ps small hd f1 ->
    decrease_pred fs ps small hd f2 ->
    decrease_pred fs ps small hd (Fbinop b f1 f2)
  | Dec_flet: forall (small: list vsymbol) (hd: vsymbol) (t1: term)
    (v: vsymbol) (f: formula),
    decrease_fun fs ps small hd t1 ->
    decrease_pred fs ps small hd f ->
    decrease_pred fs ps small hd (Flet t1 v f)
  | Dec_fif: forall (small: list vsymbol) (hd: vsymbol) 
    (f1 f2 f3: formula),
    decrease_pred fs ps small hd f1 ->
    decrease_pred fs ps small hd f2 ->
    decrease_pred fs ps small hd f3 ->
    decrease_pred fs ps small hd (Fif f1 f1 f2)
    .
    
(*TODO: write decidable version*)

Require Import IndTypes.
From Equations Require Import Equations.
(*Now let's see what the signature for such a function looks like*)

(*Want: Definition _ : forall (f: funsym) (srts: list sort),
  arg_list (domain (dom_aux pd)) (funsym_sigma_args f srts) ->
  domain (dom_aux pd (funsym_sigma_ret f srts))
  *)

Section FunDef.


Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
{pd: pi_dom} (all_unif: forall m, mut_in_ctx m gamma -> IndTypes.uniform m)
  {vt: @val_typevar sigma} {pf: pi_funpred gamma_valid pd}.
 
Notation domain := (domain (dom_aux pd)).
Notation val x :=  (v_subst (v_typevar vt) x).


(*We will handle mutual recursion by giving an index*)
(*i is the index of the function that we build - TODO: should this
  be bounded/dependent*)

(*This is the "inner" function, assuming we already have the argument
  that is recursive*)
(*Require Import Denotational.*)
Require Import Hlist.

(*TODO: where do we need the bodies?*)
Variable (fs: list fn) (ps: list pn).
Print well_founded.
(*Assume we have some relation (TODO: need to find out which)*)
(*TODO: on domains, will have precondition that they are adt*)
Axiom adt_smaller: forall (ty: vty),
(domain (val ty)) ->
(domain (val ty)) ->
Prop.
Axiom adt_smaller_wf: forall (ty: vty),
  well_founded (adt_smaller ty).

(*Need to lift this to arg list*)
(*TODO: relate to above, need def*)
Axiom arg_list_smaller: forall (idx: nat) (srts: list sort),
  arg_list domain srts ->
  arg_list domain srts -> Prop.
Axiom arg_list_smaller_wf : forall (idx: nat) (srts: list sort),
  well_founded (arg_list_smaller idx srts).

(*TODO: need to prove our relation on pairs is well-founded*)

(*Should do the well-founded proofs I think, at least
  seeing how they fit together*)
(*OR: assume well-founded and then see what we need/have
  in the recursive cases*)
(*TODO: is there a better way to handle this return type?*)
(*We could say that i is between 0 and length fs + length ps
  and then produce a list of all the return types (with map)
  and just take nth i from there - could be weird with Type though
  will have to construct bool and correct index in function*)


(*Really, we need the relation on pairs: our input should*)

(*OK: here's what I think:
  We have the lists fs and ps
  So the recursive input is: bool * nat * arg_list
  arg_list also depends on the input type
  because we need to know if funsym_sigma_args or predsym_sigma_args
  or maybe {b: bool & {i: nat | if b then i < length fs else i < length ps}} * arg_list
  then the return type is:
  (if b then domain (funsym_sigma_ret (nth i fs) srts) else bool)

  *)

Print pi_funpred.
(*TODO: move*)
Definition ps_d : predsym := 
    Build_predsym EmptyString nil nil eq_refl eq_refl.
Definition fs_d : funsym :=
    Build_funsym EmptyString nil nil vty_int eq_refl eq_refl eq_refl.

Definition build_indfun (small: list vsymbol) 
(hd: string) (hd_ty: vty)
(hd_idx: nat) (vv: val_vars pd vt) (body: term) (ty: vty) 
(*(arg: domain (dom_aux pd) (v_subst (v_typevar vt)) ty)*)
(Hty: term_has_type sigma body ty)
(Hdec: decrease_fun fs ps small (hd, hd_ty) body)
(Hinvar: forall x, In x (map fst small) ->
  adt_smaller _ (vv (x, hd_ty)) (vv (hd, hd_ty)))
(*Then, the actual inputs to the function*)
(srts: list sort)
(args: {b: bool & {t: {i : nat | i < if b then length fs else length ps} &
  arg_list domain (if b then (funsym_sigma_args (nth (proj1_sig t) (map fn_name fs) fs_d) srts) 
    else (predsym_sigma_args (nth (proj1_sig t) (map pn_name ps) ps_d) srts))}}) :
(if (projT1 args) then domain (funsym_sigma_ret (nth (proj1_sig (projT1 (projT2 args))) (map fn_name fs) fs_d) srts)
  else bool).
Proof.
  revert args.
  apply (@Fix _ _ 
    (arg_list_smaller_wf hd_idx (funsym_sigma_args f srts))
    (fun _ => domain (funsym_sigma_ret f srts))).
  (*So this is the function body that we need*)
  intros.

  (*Let's try this manually*)

(*First, we give the inner function that we will give to Fix*)
(*This is a Fixpoint for the term/formula rep recursion*)
Fixpoint indfun_term_rep (i: nat) (small: list vsymbol) 
(hd: string) (hd_ty: vty) (f: funsym)
(hd_idx: nat) (vv: val_vars pd vt) (body: term) (ty: vty) 
(*(arg: domain (dom_aux pd) (v_subst (v_typevar vt)) ty)*)
(Hty: term_has_type sigma body ty)
(Hdec: decrease_fun fs ps small (hd, hd_ty) body)
(Hinvar: forall x, In x (map fst small) ->
  adt_smaller _ (vv (x, hd_ty)) (vv (hd, hd_ty)))
(*Then, the actual inputs to the function*)
(srts: list sort)
(args: arg_list domain (funsym_sigma_args f srts))
(rec: forall y: arg_list domain (funsym_sigma_args f srts),
  arg_list_smaller hd_idx (funsym_sigma_args f srts) y args ->
  domain (funsym_sigma_ret f srts)) {struct body} :
domain (funsym_sigma_ret f srts) :=
match body with
|
(*TODO: need to have formulas too, and not using mutual recursion at all*)




(*Most generic: assume we have the vsymbol and SOME 
  list such that [decrease_fun] holds; we will instatiate them
  later. We will need another hypothesis about the invariant
  of the list (relating to valuation most likely)*)
Program Fixpoint build_indfun (i: nat) (small: list vsymbol) 
  (hd: string) (hd_ty: vty) (f: funsym)
  (hd_idx: nat) (vv: val_vars pd vt) (body: term) (ty: vty) 
  (*(arg: domain (dom_aux pd) (v_subst (v_typevar vt)) ty)*)
  (Hty: term_has_type sigma body ty)
  (Hdec: decrease_fun fs ps small (hd, hd_ty) body)
  (Hinvar: forall x, In x (map fst small) ->
    adt_smaller _ (vv (x, hd_ty)) (vv (hd, hd_ty)))
  (*Then, the actual inputs to the function*)
  (srts: list sort)
  (args: arg_list domain (funsym_sigma_args f srts))
  (H: well_founded (arg_list_smaller hd_idx (funsym_sigma_args f srts)))
  {wf  args}  :
  domain (funsym_sigma_ret f srts)
  :=
  match (domain_ne pd (val vt ty)) with
      | DE x => x 
      end. 
  
  .
  by wf args (arg_list_smaller_wf hd_idx (funsym_sigma_args f srts)) := .
  domain (dom_aux pd (funsym_sigma_ret f srts))
  (args: )


Definition build_functions (fs: list (fn * term)) (ps: list (pn * formula)) :
  forall (i: nat) (Hi: i < length fs + length ps)




(*Now we will (try to) write an inductive relation on [adt_rep]s
  (or maybe domains) that is well-founded, expressing the "structurally
  smaller" relation*)
(*Typecasting will be annoying*)
Inductive adt_smaller (m: mut_adt) (a: alg_datatype):  



  that is 
  of ADTS
  that is *)

Print pi_dom.
Search adt_rep.
Check find_constr_rep.
Search mk_adts.
Print adt_rep.


find_constr_rep:
  forall {s : sig} {gamma : context} (gamma_valid : valid_context s gamma)
	(m : mut_adt) (m_in : mut_in_ctx m gamma) (srts : list sort)
    (srts_len : Datatypes.length srts = Datatypes.length (m_params m))
    (domain_aux : sort -> Set) (t : alg_datatype) 
    (t_in : adt_in_mut t m)
    (dom_adts : forall (a : alg_datatype) (Hin : adt_in_mut a m),
                domain domain_aux (typesym_to_sort (adt_name a) srts) =
                adt_rep m srts domain_aux a Hin),
  uniform m ->
  forall x : adt_rep m srts domain_aux t t_in,
  {f : funsym &
  {Hf
  : constr_in_adt f t *
    arg_list (domain domain_aux) (funsym_sigma_args f srts)
  | x =
    constr_rep gamma_valid m m_in srts srts_len domain_aux t t_in f 
      (fst Hf) dom_adts (snd Hf)}}



      Notation term_rep := (term_rep gamma_valid pd all_unif vt pf).
      Notation formula_rep := (formula_rep gamma_valid pd all_unif vt pf).