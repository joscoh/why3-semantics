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

Definition check_decrease_fun (funs: list (lsymbol * CoqBigInt.t))
  (small: Svs.t) (hd: option vsymbol) (m: mut_adt) (vs: list ty_c) (t: term_c) : 
  errorHashconsT ty_c bool :=
  @term_rec (Svs.t -> option vsymbol -> errorHashconsT ty_c bool)
  (*Tvar*)
  (fun _ _ _ => errst_ret true)
  (*Tconst*)
  (fun _ _ _ => errst_ret true)
  (*Tapp*)
  (fun f ts recs small hd => 
    match list_find_opt (fun y => ls_equal f (fst y)) funs with
  | Some (_, i) =>
      (*Needs to be called on smaller variable at ith index*)
      match (IntFuncs.big_nth ts i) with
      | None => errst_ret false
      | Some tm => 
        match t_node_of tm with
        | Tvar x => (*Check that map is uniform*)
        (*TODO: do we need this check?*)
        l <- ls_arg_inst f ts;;
        a <- errst_list (map (fun x => x small hd) recs);;
        errst_ret (Svs.contains small x &&
        check_unif_map l &&
        forallb (fun x => x) a)
        | _ => errst_ret false
        end
      end
  | None => (*not recursive*)
    a <- errst_list (map (fun x => x small hd) recs);;
    errst_ret (forallb (fun x => x) a)
  end)
  (*Tif*)
  (fun _ rec1 _ rec2 _ rec3 small hd =>
    r1 <- rec1 small hd ;;
    r2 <- rec2 small hd ;;
    r3 <- rec3 small hd ;;
    errst_ret (r1 && r2 && r3))
  (*Tlet*)
  (fun _ rec1 x _ rec2 small hd =>
    r1 <- rec1 small hd;;
    (*TODO: is this remove useless because x is guaranteed to be fresh?
      Now need this check because x is not guaranteed to be fresh*)
    r2 <- rec2 (Svs.remove x small) (upd_option hd x) ;;
    errst_ret (r1 && r2)
  )
  (*Other interesting case is Tcase*)
  (fun (t: term_c) rec1 recps (small : Svs.t) hd =>
    r1 <- rec1 small hd;;
    r2 <- errst_list (map (fun y =>
      let  '(p, t1, rec) := y in 
      let toadd := match t_node_of t with 
        | Tvar mvar => if check_var_case small hd mvar then pat_constr_vars m vs p else Svs.empty
        | Tapp c tms => get_constr_smaller small hd m vs c tms p
        | _ => Svs.empty
      end in
      let newsmall := Svs.union toadd (Svs.diff small (pat_vars_of p)) in
      rec newsmall (upd_option_iter hd (pat_vars_of p))
    ) recps);;
    errst_ret (r1 && forallb (fun x => x) r2))
  (*Teps*)
  (fun v t rec small hd =>
    rec (Svs.remove v small) (upd_option hd v) )
  (*Tquant*)
  (fun _ vars _ rec small hd =>
    rec (svs_remove_all vars small) (upd_option_iter hd (Svs.of_list vars)))
  (*Tbinop*)
  (fun _ _ rec1 _ rec2 small hd =>
    r1 <- rec1 small hd;; 
    r2 <- rec2 small hd;;
    errst_ret (r1 && r2))
  (*Tnot*)
  (fun _ rec small hd => rec small hd)
  (*Ttrue*)
  (fun _ _ => errst_ret true)
  (*Tfalse*)
  (fun _ _ => errst_ret true) t small hd.