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


(* Declarations *)
(* 
(*NOTE: NOT hashconsing for now (see if we need/how fast)*)
Definition mk_decl node news :=
  {| d_node := node; d_news := news; d_tag := CoqWeakhtbl.dummy_tag |}. *)

(*TODO: equal and hash - use functions from hashcons basically
  because we can't use tag without hashconsing*)

Definition IllegalTypeAlias (t: tysymbol_c) : errtype :=
  mk_errtype "IllegalTypeAlias" t.
Definition ClashIdent (i: ident) : errtype :=
  mk_errtype "ClashIdent" i.
Definition BadLogicDecl (x: lsymbol * lsymbol) : errtype :=
  mk_errtype "BadLogicDecl" x.
Definition BadConstructor (l: lsymbol) : errtype :=
  mk_errtype "BadConstructor" l.

Definition BadRecordField (l: lsymbol) : errtype :=
  mk_errtype "BadRecordField" l.
Definition RecordFieldMissing (l: lsymbol) : errtype :=
  mk_errtype "RecordFieldMissing" l.
Definition DuplicateRecordField (l: lsymbol) : errtype :=
  mk_errtype "DuplicateRecordField" l.


Definition EmptyDecl : errtype :=
  mk_errtype "EmptyDecl" tt.
Definition EmptyAlgDecl (t: tysymbol_c) : errtype :=
  mk_errtype "EmptyAlgDecl" t.
Definition EmptyIndDecl (l: lsymbol) : errtype :=
  mk_errtype "EmptyIndDecl" l.

Definition NonPositiveTypeDecl (x: ocaml_tup3 tysymbol_c lsymbol ty_c) : errtype :=
  mk_errtype "NonPositiveTypeDecl" x.

Definition news_id (s : Sid.t) (i: ident) : errorM Sid.t := 
  Sid.add_new (ClashIdent i) i s.

(*Create abstract type decl*)
Definition create_ty_decl (t: tysymbol_c) : st (hashcons_ty decl) decl :=
  mk_decl (Dtype t) (Sid.singleton (ts_name_of t)).

Definition is_nodef {A: Type} (t: type_def A) : bool :=
  match t with
  | NoDef => true
  | _ => false
  end.

  (*TODO: should try to generalized with monad - lots of these
    floating around, need to fix*)
Definition foldl_errst {A B C: Type}
  (f: A -> B -> errState C A) :=
  fix foldM (l: list B) (x: A) :=
  match l with
  | nil => errst_ret x
  | h :: t =>
    j <- f x h ;;
    foldM t j
  end.

Definition foldl_err {A B: Type}
  (f: A -> B -> errorM A) :=
  fix foldM (l: list B) (x: A) :=
  match l with
  | nil => err_ret x
  | h :: t =>
    (j <- f x h ;;
    foldM t j)%err
  end.

Definition iter_err {A: Type}
  (f: A -> errorM unit) (l: list A) : errorM unit :=
  foldl_err (fun _ x => f x) l tt.

(*TODO: bad*)
Fixpoint fold_left2_err {A B C : Type} 
  (f: C -> A -> B -> errorM C) (accu: C) 
  (l1: list A) (l2: list B) : errorM (option C) :=
  match l1, l2 with
  | nil, nil => err_ret (Some accu)
  | a1 :: l1, a2 :: l2 => 
    (x <- (f accu a1 a2) ;;
    fold_left2_err f x l1 l2)%err
  | _, _ => err_ret None
  end.

Definition opt_get_exn {A: Type} (e: errtype) (x: option A) : errorM A :=
  match x with
  | Some y => err_ret y
  | None => throw e
  end.

(*Create datatype decl - checks for well-formedness (including of
  constructors and projections) and positivity (ignoring polymorphism
  and function types)*)
Definition create_data_decl (tdl: list data_decl) : 
  errState (hashcons_ty ty_c * hashcons_ty decl) decl :=
  if null tdl then errst_lift2 (throw EmptyDecl)
  else
    (*All typesymbols defined*)
    let tss := fold_left (fun s x => Sts.add (fst x) s) tdl Sts.empty : Sts.t in 

  (*For projections: need 1 argument, type needs to match ADT,
    must be marked as projection, not marked as constructor
    Then these are added to the set of identifiers*)
  let check_proj (tyv: ty_c) (s: Sls.t) (tya: ty_c) (ls: option lsymbol) : errorM Sls.t :=
    match ls with
    | None => err_ret s
    | Some ls1 =>
      match ls1.(ls_args), ls1.(ls_value), ls1.(ls_proj) with
      | ptyv :: nil, Some ptya, true =>
        if CoqBigInt.is_zero ls1.(ls_constr) then
          (_ <- ty_equal_check tyv ptyv ;;
          _ <- ty_equal_check tya ptya ;;
          Sls.add_new (DuplicateRecordField ls1) ls1 s)%err
        else throw (BadRecordField ls1)

      | _, _, _ => throw (BadRecordField ls1)
      end
    end
  in

  let check_constr (tys: tysymbol_c) (ty: ty_c) (cll: CoqBigInt.t) 
    (pjs: Sls.t) (news: Sid.t) (c: constructor) : errorM Sid.t :=
    let '(fs, pl) := c in
    (*Check claimed type value*)
    (ty1 <- opt_get_exn (BadConstructor fs) fs.(ls_value) ;;
    _ <- ty_equal_check ty ty1;;
    (*Ensure all projectors well formed*)
    o <- (fold_left2_err (check_proj ty) Sls.empty fs.(ls_args) pl);;
    match o with
    | None => throw (BadConstructor fs)
    | Some fs_pjs =>
      (*Ensure claimed projectors equal*)
      if negb (Sls.equal pjs fs_pjs) then
        x <- (Sls.choose (Sls.diff pjs fs_pjs));; (*guaranteed to succeed here*)
        throw (RecordFieldMissing x)
      (*Ensure claimed constructor number val correct*)
      else if negb (CoqBigInt.eqb fs.(ls_constr) cll) then
        throw (BadConstructor fs)
      else
        let vs := ty_freevars Stv.empty ty in
        (*Check for some positivity restrictrions:
          namely, we cannot have list A = foo : list (list A) - typesymbol
          cannot appear in arguments
          (NOTE: I think there is an easier way to check this - just
          recurse into arguments and see if typesymbol there, but longer to write)*)
        (*Should put in separate function for proving purposes later*)
        let fix check (seen: bool) (ty: ty_c) : errorM unit :=
          match ty_node_of ty with
          | Tyvar v =>
            if Stv.mem v vs then err_ret tt else throw (UnboundTypeVar v)
          | Tyapp ts tl =>
            let now1 := Sts.mem ts tss in
            if seen && now1 then throw (NonPositiveTypeDecl (to_tup3 (tys, fs, ty)))
            else iter_err (check (seen || now1)) tl
          end
        in
      _ <- iter_err (check false) fs.(ls_args);; 
      (*Finally, check name*)
      news_id news fs.(ls_name)
    end
    )%err
  in



  let check_decl (news : Sid.t) (d: data_decl) :=
    let '(ts, cl) := d in
    let cll := IntFuncs.int_length cl in
    if null cl then errst_lift2 (throw (EmptyAlgDecl ts))
    else if negb (is_nodef (ts_def_of ts)) then 
      errst_lift2 (throw (IllegalTypeAlias ts))
    else
      news1 <- errst_lift2 (news_id news (ts_name_of ts)) ;;
      (*I think just all lsymbols in cl - list of projections*)
      let pjs := fold_left (fun s y =>
        let pl := snd y in
        fold_left (opt_fold Sls.add_left) pl s) cl Sls.empty in
      (*Make sure every name in pjs is unique*)
      
      (*Cannot use errorM directly because of universe inconsistency;
        do our own ad-hoc error handling*)
      match (Sls.fold (fun (pj: lsymbol) (s : Sid.t + ident) => 
        match s with
        | inr err => inr err
        | inl s1 =>
          let ls := pj.(ls_name) in
          if Sid.contains s1 ls then inr ls else inl (Sid.add ls s1)
        end) pjs (inl news1)) with
      | inr l => errst_lift2 (throw (ClashIdent l))
      | inl news2  =>
        l1 <- errst_lift1 (st_list (map ty_var (ts_args_of ts)));;
        ty <- ty_app ts l1 ;;
        errst_lift2 (foldl_err (check_constr ts ty cll pjs) cl news2) 
      end
  in
  news <- errst_tup1 (foldl_errst check_decl tdl Sid.empty);;
  errst_tup2 (errst_lift1 (mk_decl (Ddata tdl) news)).

(*Create abstract logical param decl*)
Definition create_param_decl (ls: lsymbol) : errState (hashcons_ty decl) decl :=
  if negb (CoqBigInt.is_zero ls.(ls_constr)) || ls.(ls_proj)
  then errst_lift2 (throw (UnexpectedProjOrConstr ls))
  else 
    let news := Sid.singleton ls.(ls_name) in
    errst_lift1 (mk_decl (Dparam ls) news).

(*Create recursive fun/pred decl. Unlike current Why3 impl,
  we do not check termination here: only later when we know
  mutual types in context*)
Definition create_logic_decl_nocheck (ldl: list logic_decl) : 
  errorHashconsT decl decl :=
  if null ldl then errst_lift2 (throw EmptyDecl)
  else
    let check_decl (news : Sid.t) (x: logic_decl) : errorM Sid.t :=
      let '(ls, (s, _, _)) := x in
      if negb (ls_equal s ls) then throw (BadLogicDecl (ls, s))
      else if negb (CoqBigInt.is_zero ls.(ls_constr)) ||
        ls.(ls_proj) then throw (UnexpectedProjOrConstr ls)
      else news_id news ls.(ls_name)
    in
    news <- errst_lift2 (foldl_err check_decl ldl Sid.empty);;
    errst_lift1 (mk_decl (Dlogic ldl) news).

(*Inductive Predicate Checks*)

Definition InvalidIndDecl (x: lsymbol * prsymbol) : errtype :=
  mk_errtype "InvalidIndDecl" x.
Definition NonPositiveIndDecl (x: lsymbol * prsymbol * lsymbol) : errtype :=
  mk_errtype "NonPositiveIndDecl" x.

(*We differ from Why3, giving a simpler well-formed/positivity
  check that we proved correct in the semantics.
  We use strict positivity rather than their positivity;
  all of the tests still pass*)
Definition lsyms_notin_tm (p: Sls.t) (t: term_c) : bool :=
  Sls.for_all (fun x => negb (ls_in_tm x t)) p.

Fixpoint ind_strict_pos (sps: Sls.t) (f: term_c) {struct f} : bool :=
  lsyms_notin_tm sps f ||
  match t_node_of f with
  | Tapp p tms => Sls.mem p sps && forallb (lsyms_notin_tm sps) tms
  | Tbinop Timplies f1 f2 => ind_strict_pos sps f2 && lsyms_notin_tm sps f1
  | Tquant q tq => let '(_, _, f) := t_view_quant tq in ind_strict_pos sps f
  | Tbinop b f1 f2 =>
    match b with
    | Tiff => false
    | _ => (*and/or*) ind_strict_pos sps f1 && ind_strict_pos sps f2
    end
  (*TODO: too restrictive?*)
  | Tlet t tb => let '(_, t2) := t_view_bound tb in
    ind_strict_pos sps t2 && lsyms_notin_tm sps t
  | Tif f1 f2 f3 =>
    lsyms_notin_tm sps f1 && ind_strict_pos sps f2 && ind_strict_pos sps f3
  | Tcase t pats =>
      (*Maybe too restrictive*)
    lsyms_notin_tm sps t &&
    forallb (fun x => let '(_, t) := t_view_branch x in ind_strict_pos sps t) pats
  | _ => false
  end.

Fixpoint ind_pos (sps: Sls.t) (f: term_c) {struct f} : bool :=
  match t_node_of f with
  | Tapp p ts =>  Sls.mem p sps && forallb (lsyms_notin_tm sps) ts
  | Tquant Tforall tq => ind_pos sps (snd (t_view_quant tq))
  | Tlet t tb => (*TODO: too restrictive?*) lsyms_notin_tm sps t &&
    ind_pos sps (snd (t_view_bound tb))
  | Tbinop Timplies f1 f2 => ind_strict_pos sps f1 && ind_pos sps f2
  | _ => false
  end.

(*Shape of inductive predicates*)
Fixpoint valid_ind_form (ps: lsymbol) (f: term_c) : option term_c :=
  match t_node_of f with
  | Tapp p ts => if ls_equal p ps && 
     list_eqb ty_equal p.(ls_args) (rem_opt_list (map t_ty_of ts))
    then Some f else None (*TODO: do we need this check?*)
    (*NOTE: ignore length, implied by typing*)
  | Tbinop Timplies f1 f2 => valid_ind_form ps f2
  | Tquant Tforall tq => valid_ind_form ps (snd (t_view_quant tq))
  | Tlet t tb => valid_ind_form ps (snd (t_view_bound tb))
  | _ => None
  end.

Definition create_ind_decl (s: ind_sign) (idl: list ind_decl) :
  errorHashconsT decl decl :=
  if null idl then errst_lift2 (throw EmptyDecl)
  else
    let sps := fold_left (fun acc x => Sls.add (fst x) acc) idl Sls.empty in
    let check_ax (ps : lsymbol) (news: Sid.t) (x: prsymbol * term_c) : errorM Sid.t :=
      let '(pr, f) := x in
      (f <- check_fvs f ;;
      (*TODO: should return lsym that actually causes problem, not ps*)
      if negb (ind_pos sps f) then throw (NonPositiveIndDecl(ps, pr, ps))
      else match valid_ind_form ps f with
        | Some g =>
          let gtv := TermFuncs.t_ty_freevars Stv.empty g in
          let ftv := TermFuncs.t_ty_freevars Stv.empty f in
          if negb (Stv.subset ftv ftv) then
            (y <- (Stv.choose (Stv.diff ftv gtv));;
            throw (UnboundTypeVar y))%err
          else news_id news pr.(pr_name)
        | None => throw (InvalidIndDecl (ps, pr))
      end)%err
    in
    let check_decl (news: Sid.t) (x: lsymbol * list (prsymbol * term_c)) : errorM Sid.t :=
      let '(ps, al) := x in
      if null al then throw (EmptyIndDecl ps)
      else if isSome ps.(ls_value) then throw (TermFuncs.PredicateSymbolExpected ps)
      else
        (news <- news_id news ps.(ls_name) ;;
        foldl_err (check_ax ps) al news )%err
    in
    news <- errst_lift2 (foldl_err check_decl idl Sid.empty) ;;
    errst_lift1 (mk_decl (Dind (s, idl)) news).

(*Prop Decl*)
Definition create_prop_decl (k: prop_kind) (p: prsymbol) (f: term_c) : 
  errorHashconsT decl decl :=
  news <- errst_lift2 (news_id Sid.empty p.(pr_name)) ;;
  f <- errst_lift2 (check_fvs f) ;;
  errst_lift1 (mk_decl (Dprop (to_tup3 (k, p, f))) news).

(*Used Symbols*)

Definition syms_ts (s : Sid.t) (ts : tysymbol_c) := 
  Sid.add (ts_name_of ts) s.

Definition syms_ls (s : Sid.t) (ls : lsymbol) := 
  Sid.add ls.(ls_name) s.

Definition syms_ty (s : Sid.t) (ty : ty_c) := 
  ty_s_fold syms_ts s ty.

Definition syms_term (s : Sid.t) (t: term_c) : Sid.t := 
  t_s_fold syms_ty syms_ls s t.

Definition syms_ty_decl (ts : tysymbol_c) : Sid.t :=
  type_def_fold syms_ty Sid.empty (ts_def_of ts).

Definition syms_data_decl (tdl : list data_decl) : Sid.t :=
  let syms_constr syms '(fs,_) :=
    fold_left syms_ty fs.(ls_args) syms in
  let syms_decl syms '(_,cl) :=
    fold_left syms_constr cl syms in
  fold_left syms_decl tdl Sid.empty.

Definition syms_param_decl (ls : lsymbol) : Sid.t :=
  let syms := opt_fold syms_ty Sid.empty ls.(ls_value) in
  fold_left syms_ty ls.(ls_args) syms.

Definition syms_logic_decl (ldl : list logic_decl) : Sid.t :=
  let syms_decl syms '(ls,ld) :=
    (*Use option version so we don't need to be in error monad
      (TODO: make sure that if [ls_defn_of_axiom] succeeds, 
      then so does [open_ls_defn]. I believe this is true)*)
    match (open_ls_defn_aux ld) with
    | Some (_, e) =>
        let syms := fold_left syms_ty ls.(ls_args) syms in
        syms_term syms e
    | None => syms (*TODO: make sure we can't hit this case*)
    end
  in
  fold_left syms_decl ldl Sid.empty.

Definition syms_ind_decl (idl: list ind_decl): Sid.t :=
  let syms_ax syms '(_,f) :=
    syms_term syms f in
  let syms_decl syms '(_,al) :=
    fold_left syms_ax al syms in
  fold_left syms_decl idl Sid.empty.

Definition syms_prop_decl (f : term_c) : Sid.t :=
  syms_term Sid.empty f.

Definition get_used_syms_ty (ty : ty_c) := 
  syms_ty Sid.empty ty.

Definition get_used_syms_decl (d: decl) : Sid.t :=
  match d.(d_node) with
  | Dtype ts => syms_ty_decl ts
  | Ddata dl => syms_data_decl dl
  | Dparam ls => syms_param_decl ls
  | Dlogic ldl => syms_logic_decl ldl
  | Dind (_, idl) => syms_ind_decl idl
  | Dprop x => let '(_, _, f) := of_tup3 x in syms_prop_decl f
  end.
  
  
  
  
  