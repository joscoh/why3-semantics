Require Import TermDefs TermFuncs DeclDefs DeclFuncs TheoryFuncs TaskDefs TransDefs.
Import MonadNotations.
Local Open Scope errst_scope.
(*TODO: do eliminate_builtin later probably - relies heavily on metas*)


(** Eliminate definitions of functions and predicates *)

(*Basically takes term to hd = t
  BUT does inside statements:
  so function if b then t1 else t2 gives
  if b then (hd = t1) else (hd = td)
  (probably just optimization)
  
  More usefully, say we have length function, this gives
  match l with | nil -> length(l) = 0 | x :: xs -> length (l) = 1 + length xs
  *)
Fixpoint t_insert (hd t : term_c) : errorHashconsT ty_c term_c := 
  match t_node_of t with
  | Tif f1 t2 t3 =>
    t1 <- (t_insert hd t2);;
    t2 <- (t_insert hd t3);;
    errst_lift2 (t_if f1 t1 t2)
  | Tlet t1 bt =>
    let '(v,t2) := t_view_bound bt in
    t2 <- (t_insert hd t2);;
    errst_lift2 (t_let_close v t1 t2)
  | Tcase tl bl =>
      let br b :=
        let '(pl,t1) := t_view_branch b in
        t2 <- (t_insert hd t1);;
        errst_ret (t_close_branch pl t2)
      in
      l <- errst_list (map br bl) ;;
      errst_lift2 (t_case tl l)
  | _ => TermTFAlt.t_selecti t_equ_simp (fun t1 t2 => errst_lift2 (t_iff_simp t1 t2)) hd t
  end.

Axiom meta_rewrite : meta.

  (*For single lsymbol:
    ex: function fact(n) = if n = 0 then 1 else n * fact(n-1)*)
  (*Just using all things in hashcons state even though we don't need 1*)
Definition add_ld (which : lsymbol -> bool) md x ds :
  errState (CoqBigInt.t * hashcons_full) 
    (list decl * list logic_decl * list decl * list tdecl_c) :=
  let '(ls,ld) := x in
  let '(abst,defn,axl,metas) := ds in

  if which ls then

    y <- errst_lift2 (open_ls_defn ld) ;;
    let '(vl, e) := y in
    (*vl = [n], e = if n = 0 then 1 else n * fact(n-1)*)
    let nm := (ls.(ls_name).(id_string) ++ "'def")%string in
    pr <- errst_tup1 (errst_lift1 (create_prsymbol (id_derive1 nm ls.(ls_name)))) ;;
    (*pr is prsymbol of fact_def*)
    hd <- errst_tup2 (full_of_ty (t_app ls (List.map t_var vl) (t_ty_of e)));;
    (*hd = fact(n) (as term)*)
    ti <- errst_tup2 (full_of_ty (t_insert hd e)) ;;
    ax <- errst_lift2 (t_forall_close vl [] ti)  ;;
    (*ax: forall n, if n = 0 then fact(n) = 1 else fact(n) = n * fact (n-1)*)
    ax <- errst_tup2 (full_of_d (create_prop_decl Paxiom pr ax)) ;;
    (*create abstract symbol for fact*)
    ld <- errst_tup2 (full_of_d (create_param_decl ls)) ;;
    (*metas, whatever*)
    metas <-
      if Sls.mem ls md then
        m <- errst_tup2 (full_of_ty_td (TheoryFuncs.create_meta meta_rewrite [MApr pr]));;
        errst_ret (m :: metas)
      else errst_ret metas ;;
    (*defn are defined things, ld are abstract symbols, axl are axioms*)
    errst_ret (ld :: abst, defn, ax :: axl, metas)
  else
    errst_ret (abst, (ls,ld) :: defn, axl, metas).

    (*add_ld should create abstract syms, definition, axioms, (metas)*)
Definition elim_decl which meta_rewrite_def (l : list logic_decl) :
  errState (CoqBigInt.t * hashcons_full) (list tdecl_c) :=
  x <- foldr_errst (add_ld which meta_rewrite_def) ([],[],[],[]) l ;;
  let '(abst,defn,axl,metas) := x in
  (* ms <- errst_tup2 (full_of_td metas) ;; *)
  defn <- errst_tup2 (full_of_d (if null defn then errst_ret [] else l <- create_logic_decl_nocheck defn ;; errst_ret [l])) ;;
  r1 <- (errst_tup2 (full_of_td (errst_lift1 (st_list (rev_map create_decl (abst ++ defn ++ axl)))))) ;;
  errst_ret (rev_append r1 metas).

Definition create_decl_list (d: decl) :
  errState (CoqBigInt.t * hashcons_full) (list tdecl_c) :=
   d1 <- errst_tup2 (full_of_td (errst_lift1 (create_decl d)));;
  errst_ret [d1].

  (*Main one: calls elim_decl - which is just boolean condition,
    d is decl*)
Definition elim which meta_rewrite_def d := 
  match d.(d_node) with
  | Dlogic l => elim_decl which meta_rewrite_def l
  | _ => create_decl_list d
  end.

Definition elim_recursion d := 
  match d.(d_node) with
  | Dlogic l =>
    if match l with | [(s, _)] => Sid.mem s.(ls_name) (get_used_syms_decl d)
    | _ => false end
      || (CoqBigInt.lt CoqBigInt.one (IntFuncs.int_length l))
    then elim_decl (fun _ => true) Sls.empty l
    else create_decl_list d
  | _ => create_decl_list d
  end.

(*NOTE: for us, all recursion is structural*)
Definition is_struct {A: Type} (dl: list (A * ls_defn)) : bool := (* FIXME? Shouldn't 0 be allowed too? *)
  forallb (fun '(_,ld) => 
    CoqBigInt.eqb (IntFuncs.int_length (ls_defn_decrease_aux ld)) CoqBigInt.one) dl.

(* FIXME? We can have non-recursive functions in a group *)
(*JOSH: irrelevant for us, skip for now*)
(* let elim_non_struct_recursion d := 
  match d.d_node with
  | Dlogic ((s,_) :: _ as dl)
    when Sid.mem s.ls_name (get_used_syms_decl d) && not (is_struct dl) ->
      elim_decl Util.ttrue Sls.empty dl
  | _ ->
      [Theory.create_decl d] *)

Definition elim_mutual d := 
  match d.(d_node) with
  | Dlogic l => if CoqBigInt.lt CoqBigInt.one (IntFuncs.int_length l) then
    elim_decl (fun _ => true) Sls.empty l
    else create_decl_list d
  | _ => create_decl_list d
  end.

(*TODO: do on_tagged after*)
(* let eliminate_definition_gen which =
  Trans.on_tagged_ls Compute.meta_rewrite_def (fun rew ->
      Trans.tdecl (elim which rew) None) *)

(* let eliminate_definition_func  =
  eliminate_definition_gen (fun ls -> ls.ls_value <> None)
let eliminate_definition_pred  =
  eliminate_definition_gen (fun ls -> ls.ls_value =  None)
let eliminate_definition       =
  eliminate_definition_gen Util.ttrue *)

Definition eliminate_recursion        := tdecl_errst elim_recursion None.
(* Definition eliminate_non_struct_recursion := tdecl_errst elim_non_struct_recursion None. *)
Definition eliminate_mutual_recursion := tdecl_errst elim_mutual None.