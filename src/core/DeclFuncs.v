Require Import Monads TyDefs TermDefs DeclDefs TyFuncs TermFuncs IdentDefs.
Import MonadNotations.
Local Open Scope err_scope.

Definition UnboundVar (v: vsymbol) : errtype :=
  mk_errtype "UnboundVar" v.
Definition UnexpectedProjOrConstr (ls: lsymbol) : errtype :=
  mk_errtype "UnexpectedProjOrConstr" ls.

Definition check_fvs (f: term_c) : errorM term_c :=
  (*TODO: can't do error directly bc of universe inconsistency - why?*)
  (* _ <- @t_v_fold (errorM unit) (fun (_: errorM unit) vs => throw (UnboundVar vs)) (err_ret tt) f ;; *)
  _ <- match t_v_fold (fun (_: option vsymbol) vs => 
    Some vs) None f with
  | Some v => throw (UnboundVar v)
  | None => err_ret tt
  end ;;
  t_prop f.

(*TODO: use option instead? changes externally visible behavior*)
Definition check_vl (t: ty_c) (v: vsymbol) : errorM unit :=
  ty_equal_check t v.(vs_ty).
(*So the term is not actually the body, it is the formula:
  forall x, f (x) = t (or forall x, p(x) <-> f)
  not sure why they do it this way, guess it is consistent
  with quantifiers.
  At least it is relatively straightforward to go back and forth
  This is how one creates a [logic_decl], then passes
  it in to create a full decl *)

(*TODO: move*)
Definition map2_opt {A B C: Type} (f: A -> B -> C) :=
    fix map2 (l1: list A) (l2: list B) : option (list C) :=
      match l1, l2 with
      | nil, nil => Some nil
      | x1 :: t1, x2 :: t2 => 
        match (map2 t1 t2) with
        | Some l1 => Some (f x1 x2 :: l1)
        | None => None
        end
      | _, _ => None
      end.

(*TODO: option or error?*)
Definition list_iter2 {A B: Type} (f: A -> B -> errorM unit) :=
  fix list_iter2  (l1 : list A) (l2: list B) : errorM unit :=
    match l1, l2 with
    | nil, nil => err_ret tt
    | x1 :: t1, x2 :: t2 => 
      _ <- f x1 x2 ;;
      list_iter2 t1 t2
    | _, _ => throw (Invalid_argument "iter2")
    end.

Local Open Scope errst_scope.

Definition make_ls_defn (ls: lsymbol) (vl: list vsymbol)
(t: term_c) : errorHashconsT ty_c (lsymbol * ls_defn) :=
  (* check ls *)
  if negb (CoqBigInt.is_zero ls.(ls_constr)) || ls.(ls_proj)
    then errst_lift2 (throw (UnexpectedProjOrConstr ls))
  else
  (* check for duplicate arguments *)
  let add_v s v := Svs.add_new_opt v s in
  _ <- errst_lift2 (fold_left (fun acc x =>
    (s <- acc ;;
    match (add_v s x) with
    | Some s' => err_ret s'
    | None => throw (DuplicateVar x)
    end)%err) vl (err_ret Svs.empty)) ;;
  (* build the definition axiom *)
  hd <- t_app ls (List.map t_var vl) (t_ty_of t) ;;
  bd <- TermTFAlt.t_selecti t_equ (fun x y => errst_lift2 (t_iff x y)) 
    hd t ;;
  tforall <- errst_lift2 (t_forall_close vl [] bd) ;;
  fd <- errst_lift2 (check_fvs tforall) ;;
   (* check correspondence with the type signature of ls *)
  _ <- errst_lift2 (list_iter2 check_vl ls.(ls_args) vl) ;;
  _ <- errst_lift2 (t_ty_check t ls.(ls_value)) ;;
  (* return the definition *)
  errst_ret (ls, (ls, fd, [])).

(*Option monad for internal use, exception for API*)
Definition open_ls_defn_aux (l: ls_defn) : option 
  (list vsymbol * term_c) :=
  let '(_, f, _) := l in
  let s := match t_node_of f with
    | Tquant Tforall b => t_view_quant b
    | _ => (nil, nil, f)
    end in
  let '(vl, _, f) := s in
  match t_node_of f with
  | Tapp _ (_ :: f :: nil) => Some (vl, f)
  | Tbinop _ _ f => Some (vl, f)
  | _ => None
  end.

Definition open_ls_defn (l: ls_defn) : errorM (list vsymbol * term_c) :=
  match open_ls_defn_aux l with
  | Some (vs, t) => err_ret (vs, t)
  | None => (TermFuncs.assert_false "open_ls_defn"%string)
  end.

(*Definition open_ls_defn (l: ls_defn) : errState CoqBigInt.t 
  (list vsymbol * term_c) :=
  let '(_, f, _) := l in
  s <- errst_lift1 match t_node_of f with
    | Tquant Tforall b => t_open_quant1 b
    | _ => st_ret (nil, nil, f)
    end ;;
  let '(vl, _, f) := s in
  match t_node_of f with
  | Tapp _ (_ :: f :: nil) => errst_ret (vl, f)
  | Tbinop _ _ f => errst_ret (vl, f)
  | _ => errst_lift2 (TermFuncs.assert_false "open_ls_defn"%string)
  end.*)

  
(*Termination Checking*)
(*TODO: move to DeclDefs?*)
Definition mut_adt : Type := list data_decl.
Definition mut_info : Type := list mut_adt * Mts.t mut_adt.

(*Decidable equality for [mut_adt]*)
Definition mut_adt_eqb : mut_adt -> mut_adt -> bool :=
  list_eqb data_decl_eqb.

(*TODO: probably move*)
(*Get all mutual ADT definitions.*)
Definition get_ctx_tys (kn: Mid.t decl) : mut_info :=
  Mid.fold (fun _ d acc =>
    match d.(d_node) with
    | Ddata m =>
      let '(ms, mp) := acc in
      (m :: ms, fold_right (fun t ts => Mts.add t m ts) mp (map fst m))
    | _ => acc
    end) kn (nil, Mts.empty).

Definition is_vty_adt (ctx: mut_info) (t: ty_c) : 
  option (mut_adt * tysymbol_c * list ty_c) :=
  match ty_node_of t with
  | Tyapp ts tys => option_bind (Mts.find_opt _ ts (snd ctx))
      (fun m => Some (m, ts, tys))
  | Tyvar _ => None
  end.

Definition ts_in_mut (ts: tysymbol_c) (m: mut_adt) : bool :=
  isSome (list_find_opt (fun a => ts_equal (fst a) ts) m).

Definition vty_in_m (m: mut_adt) (vs: list ty_c) (v: ty_c) : bool :=
  match ty_node_of v with
  | Tyapp ts vs' => ts_in_mut ts m && list_eqb ty_equal vs vs'
  | _ => false
  end.

Definition vty_in_m' (m: mut_adt) (v: ty_c) : bool :=
  match ty_node_of v with
  | Tyapp ts vs' => ts_in_mut ts m
  | _ => false
  end.

(*TODO: should really use maps but complicated with tuples and lists -
  do we need BSTs?*)
Definition add_union {A: Type} (eq : A -> A -> bool) (x: A) (l: list A) :=
  if existsb (fun y => eq x y) l then l else x :: l.

Definition get_adts_present (ctx: mut_info) (l: list vsymbol) : 
  list (mut_adt * list ty_c) :=
  fold_right (fun v acc =>
    match is_vty_adt ctx (v.(vs_ty)) with
    | Some (m, a, vs) => add_union (*equality predicate*)
      (tuple_eqb mut_adt_eqb (list_eqb ty_eqb)) (m, vs) acc
    | None => acc
    end) nil l.

Definition get_idx_lists_aux kn (funs: Mls.t (list vsymbol * term_c)) :  
  list (mut_adt * list ty_c * list (list CoqBigInt.t)) :=
    let syms : list (list vsymbol) := 
      Mls.fold (fun _ x y => (fst x) :: y) funs nil in
    map (fun '(m, vs) => 
    
      let l : list (list CoqBigInt.t) :=
        map (fun args =>
          map fst (filter (fun it => vty_in_m m vs (snd it)) 
            (combine (IntFuncs.iota2 (IntFuncs.int_length args)) (map (fun v => v.(vs_ty)) args)))
        ) syms
        in
        (*If any are null, discard*)
        (m, vs, if existsb null l then [] else l)
      
    ) 
    (get_adts_present (get_ctx_tys kn) (List.concat syms)).

Definition get_idx_lists kn (funs: Mls.t (list vsymbol * term_c) ) : 
  list (mut_adt * list ty_c * list (list CoqBigInt.t)) :=
  filter (fun '(_, _, x) => negb (null x)) (get_idx_lists_aux kn funs).

Fixpoint get_possible_index_lists {A: Type} (l: list (list A)) : 
  list (list A) :=
  match l with
  | l1 :: rest => let r := get_possible_index_lists rest in
    concat (map (fun x => List.map (fun y => x :: y) r) l1)
  | [] => [[]]
  end.

(*The core of the termination checking*)
Definition check_unif_map (m: Mtv.t ty_c) : bool :=
  Mtv.for_all _ (fun (v: tvsymbol) (t : ty_c) => 
    match ty_node_of t with 
      | Tyvar v1 => tv_equal v v1 
      | _ => false
    end) m.

Definition vsym_in_m (m: mut_adt) (vs: list ty_c) (x: vsymbol) : bool :=
  vty_in_m m vs (x.(vs_ty)).

Definition constr_in_m (l: lsymbol) (m: mut_adt) : bool :=
  existsb (fun (d: data_decl) => existsb (fun c => ls_equal (fst c) l) (snd d)) m.


Fixpoint pat_constr_vars_inner (m: mut_adt) (vs: list ty_c) (p: pattern_c) {struct p} : 
  Svs.t :=
  match pat_node_of p with
| Pwild => Svs.empty
| Pvar x => if vsym_in_m m vs x then Svs.singleton x else Svs.empty
| Papp f ps => 
    (*only add variables in constructors of right type*)
    if constr_in_m f m then (*TODO: how to say tys = vs? For now, don't include - ruled out by uniformity of types
        although this is currently unsound I think (or maybe sound I just can't prove it)*)
        (*Also don't use length goals, implied by typing*)
      (*For termination purposes, fold over map2*)
      fold_right Svs.union Svs.empty 
      (map2 (fun p x => if vty_in_m' m x then pat_constr_vars_inner m vs p else Svs.empty) ps (f.(ls_args)))
        (*A horrible way to write this: need to get patterns corresponding only to argument types in m*)
      (*Also do not include params part - rely on uniform ADT restriction*)
  else Svs.empty
| Por p1 p2 => Svs.inter (pat_constr_vars_inner m vs p1) (pat_constr_vars_inner m vs p2)
| Pas p' y => Svs.union (if vsym_in_m m vs y then Svs.singleton y else Svs.empty) (pat_constr_vars_inner m vs p')
  end.

(*Get strictly smaller (not just <=) vars. Recurse until we hit constructor*)
Fixpoint pat_constr_vars (m: mut_adt) (vs: list ty_c) (p: pattern_c) : Svs.t :=
match pat_node_of p with
| Papp _ _ => pat_constr_vars_inner m vs p
| Por p1 p2 => Svs.inter (pat_constr_vars m vs p1) (pat_constr_vars m vs p2)
| Pas p y => pat_constr_vars m vs p
| _ => Svs.empty
end.

Definition upd_option (hd: option vsymbol) (x: vsymbol) : option vsymbol :=
  match hd with
  | Some y => if vs_equal x y then None else hd
  | None => None
  end.

Definition upd_option_iter (x: option vsymbol) (xs: Svs.t) : option vsymbol :=
  Svs.fold (fun v o => upd_option o v) xs x.

Definition check_var_case small hd v :=
  option_eqb vs_equal hd (Some v) || Svs.mem v small.

Definition tm_var_case (small: Svs.t) (hd: option vsymbol) (t: term_c) : bool :=
  match t_node_of t with
| Tvar v => check_var_case small hd v
| _ => false
end.

(*If jth element of tms is small variable, all [pat_constr_vars] in
  (nth j ps) should be added*)
Definition get_constr_smaller (small: Svs.t) (hd: option vsymbol) (m: mut_adt)
  (vs: list ty_c) (f: lsymbol) (tms: list term_c) (p: pattern_c) : Svs.t :=
  match pat_node_of p with
  | Papp f1 ps => if ls_equal f f1 then 
      fold_right Svs.union Svs.empty (map2 (fun t p => if tm_var_case small hd t then pat_constr_vars m vs p else Svs.empty) tms ps)
      else Svs.empty
  | _ => Svs.empty
  end.

Definition svs_remove_all (l: list vsymbol) (s: Svs.t) : Svs.t :=
  fold_right Svs.remove s l.

(*Convert a list of (option A) to a list of A*)
Definition rem_opt_list {A: Type} (l: list (option A)) : list A :=
  fold_right (fun x acc => match x with
                            | Some y => y :: acc
                            | None => acc
  end) nil l.

Definition check_decrease_fun (funs: list (lsymbol * CoqBigInt.t))
  (small: Svs.t) (hd: option vsymbol) (m: mut_adt) (vs: list ty_c) (t: term_c) : 
  bool :=
  @term_rec (Svs.t -> option vsymbol -> bool)
  (*Tvar*)
  (fun _ _ _ => true)
  (*Tconst*)
  (fun _ _ _ => true)
  (*Tapp*)
  (fun f ts recs small hd => 
    match list_find_opt (fun y => ls_equal f (fst y)) funs with
  | Some (_, i) =>
      (*Needs to be called on smaller variable at ith index*)
      match (IntFuncs.big_nth ts i) with
      | None => false
      | Some tm => 
        match t_node_of tm with
        | Tvar x => (*Check that map is uniform*)
        (*TODO: do we need this check?*)
        (* l <- ls_arg_inst f ts;; *)
        (Svs.contains small x &&
        (*NOTE: justified by proof in DeclProofs.v*)
        list_eqb ty_equal f.(ls_args) (rem_opt_list (map t_ty_of ts)) &&
        (* check_unif_map l && *)
        forallb (fun x => x) (map (fun x => x small hd) recs))
        | _ => false
        end
      end
  | None => (*not recursive*)
    (forallb (fun x => x) (map (fun x => x small hd) recs))
  end)
  (*Tif*)
  (fun _ rec1 _ rec2 _ rec3 small hd =>
    (rec1 small hd) && (rec2 small hd) && (rec3 small hd))
  (*Tlet*)
  (fun _ rec1 x _ rec2 small hd =>
    (*TODO: is this remove useless because x is guaranteed to be fresh?
      Now need this check because x is not guaranteed to be fresh*)
    (rec1 small hd) && (rec2 (Svs.remove x small) (upd_option hd x))
  )
  (*Other interesting case is Tcase*)
  (fun (t: term_c) rec1 recps (small : Svs.t) hd =>
    let r2 := (map (fun y =>
      let  '(p, t1, rec) := y in 
      let toadd := match t_node_of t with 
        | Tvar mvar => if check_var_case small hd mvar then pat_constr_vars m vs p else Svs.empty
        | Tapp c tms => get_constr_smaller small hd m vs c tms p
        | _ => Svs.empty
      end in
      let newsmall := Svs.union toadd (Svs.diff small (pat_vars_of p)) in
      rec newsmall (upd_option_iter hd (pat_vars_of p))
    ) recps) in
    (rec1 small hd) && forallb (fun x => x) r2)
  (*Teps*)
  (fun v t rec small hd =>
    rec (Svs.remove v small) (upd_option hd v) )
  (*Tquant*)
  (fun _ vars _ rec small hd =>
    rec (svs_remove_all vars small) (upd_option_iter hd (Svs.of_list vars)))
  (*Tbinop*)
  (fun _ _ rec1 _ rec2 small hd =>
    (rec1 small hd) && (rec2 small hd))
  (*Tnot*)
  (fun _ rec small hd => rec small hd)
  (*Ttrue*)
  (fun _ _ => true)
  (*Tfalse*)
  (fun _ _ => true) t small hd.
  
Definition find_idx_list (l: list (lsymbol * (list vsymbol * term_c))) m vs 
  (candidates : list (list CoqBigInt.t)) : 
  option (list CoqBigInt.t) :=
  list_find_opt (fun il => 
   (forallb (fun y =>
      let '((f, (vars, t)), i) := y in
      match IntFuncs.big_nth vars i with
      | None => false
      | Some x =>
      check_decrease_fun (List.combine (List.map fst l) il) Svs.empty (Some x) m vs t
      end
      ) (List.combine l il))) candidates.

(*TODO: move*)
Definition list_inb {A: Type} (eq: A -> A -> bool) (x: A) (l: list A) : bool :=
  existsb (fun y => eq x y) l.

(*TODO: move above*)
Definition mut_in_ctx (m: mut_adt) (kn: Mid.t decl) : bool :=
  list_inb mut_adt_eqb m (fst (get_ctx_tys kn)).

(*TODO: overlap w CommonSSR*)
Definition find_elt {A B: Type} (f: A -> option B) (l: list A) :
  option (A * B) :=
  fold_right (fun x acc => match f x with | None => acc | Some y => Some (x, y) end)
  None l.
 (*TODO: do we need mutual ADT?*)
Definition check_termination_aux kn (funs: Mls.t (list vsymbol * term_c)) :
  option (Mls.t CoqBigInt.t) :=
  if Mls.is_empty _ funs then None
  else 
    let l := Mls.bindings funs in
    let idxs := (get_idx_lists kn funs) in
  (*TODO: skipping params for now - do we need?*)
   (option_bind 
  (find_elt (fun y =>
      let '(m, vs, cands) := y in 
      (*Skip params, implied by typing*)
      if mut_in_ctx m kn then 
        find_idx_list l m vs (get_possible_index_lists cands)
    else None
      )
    idxs)
  (fun y =>
    let  '(_, idxs) := y in 
    (*Match index with corresponding symbol*)
    Some (fold_right (fun x acc => Mls.add (fst x) (snd x) acc) Mls.empty (combine (map fst l) idxs) )
  )).

Definition ls_in_tm (l: lsymbol) (t: term_c) : bool :=
  term_rec 
  (*Tvar*)
  (fun _ => false)
  (*Tconst*)
  (fun _ => false)
  (*Tapp*)
  (fun f ts recs => ls_equal f l || existsb (fun x => x) recs)
  (*Tif*)
  (fun _ r1 _ r2 _ r3 => r1 || r2 || r3)
  (*Tlet*)
  (fun _ r1 _ _ r2 => r1 || r2)
  (*Tcase*)
  (fun _ r1 recs => r1 || existsb snd recs)
  (*Teps*)
  (fun _ _ r => r)
  (*Tquant*)
  (fun _ _ _ r => r)
  (*Tbinop*)
  (fun _ _ r1 _ r2 => r1 || r2)
  (*Tnot*)
  (fun _ r => r)
  (*Ttrue*)
  false
  (*Tfalse*)
  false
  t.

(*TODO: Why doesn't this work inline?*)
Definition build_decl node news tag: decl :=
  {| d_node := node; d_news := news; d_tag := tag |}.

(*TODO*)
Definition NoTerminationProof (l: lsymbol) : errtype :=
  mk_errtype "NoTerminationProof" l.

(*First, check that all logic definitions are valid*)
Definition get_logic_defs (ld: list logic_decl) : 
  option (Mls.t (list vsymbol * term_c)) :=
  fold_left (fun acc y => 
    let '(ls, ld) := y in
    match acc, open_ls_defn_aux ld with
    | Some m, Some ld' => Some (Mls.add ls ld' m)
    | _, _ => None
    end
  ) ld (Some (Mls.empty)).

Definition check_termination_strict kn d : 
  errorM decl :=
  match d.(d_node) with
  | Dlogic (l :: ls) =>
    let ld := l :: ls in

    match (get_logic_defs ld) with
    | None => (TermFuncs.assert_false "open_ls_defn"%string)
    | Some syms =>
         (*First, see if non-recursive*)
      let binds := Mls.bindings syms in
      if forallb (fun t => forallb (fun l => negb (ls_in_tm l t)) (map fst binds)) (map (fun x => snd (snd x)) binds) 
        then err_ret d else
      match check_termination_aux kn syms with
      | Some idxs => (*TODO: do we actually need index info?*)
        (*TODO: change from int list to int maybe?*)
        let ldl := (map (fun (y : logic_decl) =>
          let '(ls,((_,f),_)) := y in 
          (ls,((ls,f),[(*TODO*) (*CoqBigInt.to_int*) 
            match Mls.find_opt _ ls idxs with
            | Some i => i
            | None => (*TODO: HACK*) CoqBigInt.neg_one
            end (*(Mls.find _ ls idxs)*)]))) ld) in (*JOSH TODO delete to_int*)
        (*TODO: do we need to hashcons?*)
        err_ret (build_decl (Dlogic ldl) (d.(d_news)) (d.(d_tag)))
      | None => (throw (NoTerminationProof (fst l)) )
      end
    end
  | _ => err_ret d
  end.

