(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* exception Bare *)

(* let rec populate (is_constr: lsymbol -> bool) (ty: ty) (css,csl as acc) p = match p.pat_node with
  | Pwild | Pvar _ -> acc
  | Pas (p,_) -> populate is_constr ty acc p
  | Por (p,q) -> populate is_constr ty (populate is_constr ty acc p) q
  | Papp (fs,pl) when is_constr fs ->
      if Mls.mem fs css then acc else
      Mls.add fs pl css, (fs,pl) :: csl
  | Papp (fs,_) -> raise (ConstructorExpected (fs,ty))

let populate_all (is_constr: lsymbol -> bool) (ty: ty) rl =
  let populate acc (pl,_) = populate is_constr ty acc (List.hd pl) in
  List.fold_left populate (Mls.empty,[]) rl *)

(* let dispatch mk_let t types rl = 
  let add_case fs pl a cases =
    Mls.change (function
      | None -> Some [pl,a]
      | Some rl -> Some ((pl,a)::rl)) fs cases
  in
  let union_cases pl a types cases =
    let add pl q = pat_wild q.pat_ty :: pl in
    let wild ql = [List.fold_left add pl ql, a] in
    let join _ wl rl = Some (List.append wl rl) in
    Mls.union join (Mls.map wild types) cases
  in
  let rec dispatch (pl,a) (cases,wilds) =
    let p = List.hd pl in let pl = List.tl pl in
    match p.pat_node with
      | Papp (fs,pl') ->
          add_case fs (List.rev_append pl' pl) a cases, wilds
      | Por (p,q) ->
          dispatch (p::pl, a) (dispatch (q::pl, a) (cases,wilds))
      | Pas (p,x) ->
          dispatch (p::pl, mk_let x t a) (cases,wilds)
      | Pvar x ->
          let a = mk_let x t a in
          union_cases pl a types cases, (pl,a)::wilds
      | Pwild ->
          union_cases pl a types cases, (pl,a)::wilds
  in
  List.fold_right dispatch rl (Mls.empty,[]) *)

(* let comp_cases compile cases tl ty cs al =
  try compile (List.rev_append al tl) (Mls.find cs cases)
  with NonExhaustive pl ->
    let rec cont acc vl pl = match vl,pl with
      | (_::vl), (p::pl) -> cont (p::acc) vl pl
      | [], pl -> pat_app cs acc ty :: pl
      | _, _ -> assert false
    in
    raise (NonExhaustive (cont [] cs.ls_args pl)) *)

(* let comp_wilds compile types tl wilds css ty () =
  match (compile tl wilds) with
  | Succ x -> Succ x
  | NonExh pl ->
    let find_cs cs =
      if Mls.mem cs types then () else
      let tm = ty_match Mtv.empty (Option.get cs.ls_value) ty in
      let wild ty = pat_wild (ty_inst tm ty) in
      let pw = pat_app cs (List.map wild cs.ls_args) ty in
      raise (NonExhaustive (pw :: pl))
    in
    Sls.iter find_cs css;
    raise (NonExhaustive (pat_wild ty :: pl)) *)

  (* try compile tl wilds
  with NonExhaustive pl ->
    let find_cs cs =
      if Mls.mem cs types then () else
      let tm = ty_match Mtv.empty (Option.get cs.ls_value) ty in
      let wild ty = pat_wild (ty_inst tm ty) in
      let pw = pat_app cs (List.map wild cs.ls_args) ty in
      raise (NonExhaustive (pw :: pl))
    in
    Sls.iter find_cs css;
    raise (NonExhaustive (pat_wild ty :: pl)) *)

(*TODO: maybe put this back in*)
(* let comp_full mk_case compile bare types tl cases wilds css cslist t ty () =
  let no_wilds =
    if bare then
      let cs,_ = Mls.choose types in
      BigInt.eq (Mls.cardinal types) (cs.ls_constr)
    else
      Mls.set_submap css types
  in
  let base = if no_wilds then []
    else 
      begin match comp_wilds compile types tl wilds css ty () with
      | NonExh pl -> raise (NonExhaustive pl)
      | Succ x ->
      
          [pat_wild ty,x ]
      end
  in
  let add acc (cs,ql) =
    let get_vs q = create_vsymbol (id_fresh "x") q.pat_ty in
    let vl = List.rev_map get_vs ql in
    let pl = List.rev_map pat_var vl in
    let al = List.rev_map t_var vl in
    begin match comp_cases compile cases tl ty cs al with
    | NonExh pl -> raise (NonExhaustive pl)
    | Succ x ->
        (pat_app cs pl ty, x) :: acc
    end
  in
  Succ (mk_case t (List.fold_left add base cslist)) *)

(* let compile ~get_constructors ~mk_case ~mk_let (bare: bool) (simpl_constr: bool) tl rl =
  compile_aux' get_constructors mk_case mk_let bare simpl_constr tl rl *)
  (* let rec compile tl rl = match tl,rl with
    | _, [] -> (* no actions *)
        let pl = List.map (fun t -> pat_wild (t_type t)) tl in
        NonExh pl  (*(NonExhaustive pl)*)
    | [], (_,a) :: _ -> (* no terms, at least one action *)
        Succ a
    | t :: tl, _ -> (* process the leftmost column *)
        let ty = t_type t in
        (* extract the set of constructors *)
        let bare,css = match ty.ty_node with
          | Tyapp (ts,_) -> if bare then (true, Sls.empty) else (false, Sls.of_list (get_constructors ts))
              (* begin try false, Sls.of_list (get_constructors ts)
              with Bare -> true, Sls.empty end *)
          | Tyvar _ -> false, Sls.empty
        in
        (* if bare, only check fs.ls_constr *)
        let is_constr fs =
          BigInt.pos fs.ls_constr && (bare || Sls.mem fs css)
        in
        (* map every constructor occurring at the head
         * of the pattern list to the list of its args *)
        let types, cslist = populate_all is_constr ty rl
        in
        (* dispatch every case to a primitive constructor/wild case *)
        let cases,wilds = dispatch mk_let t types rl in
        (* how to proceed if [t] is [Tapp(cs,al)] and [cs] is in [cases] *)
        
        (* how to proceed if [t] is not covered by [cases] *)
        
        

        (* assemble the primitive case statement *)
        if Mls.is_empty types then
          comp_wilds compile types tl wilds css ty ()
        else if simpl_constr then
          begin match t.t_node with
          (* | _ when Mls.is_empty types ->
              comp_wilds () *)
          | Tapp (cs,al) when is_constr cs ->
              if Mls.mem cs types then comp_cases compile cases tl ty cs al else comp_wilds compile types tl wilds css ty ()
          | _ -> comp_full mk_case compile bare types tl cases wilds css cslist t ty ()
              
            end
          else comp_full mk_case compile bare types tl cases wilds css cslist t ty ()
  in
  compile tl rl *)

let compile ~get_constructors ~mk_case ~mk_let (bare: bool) (simpl_constr: bool) tl rl =
  compile_aux' get_constructors mk_case mk_let bare simpl_constr tl rl

let compile_bare ~mk_case ~mk_let tl rl =
  compile_bare_aux mk_case mk_let tl rl
  (* let get_constructors _ = [] in
  try compile ~get_constructors ~mk_case ~mk_let true true tl rl
  with NonExhaustive _ -> raise (NonExhaustive []) *)

let check_compile ~get_constructors tl ps =
  check_compile_aux get_constructors tl ps
  (* function
  | [] ->
      let pl = List.map (fun t -> pat_wild (t_type t)) tl in
      raise (NonExhaustive pl)
  | (pl::_) as ppl ->
      let mkt p = t_var (create_vsymbol (id_fresh "_") p.pat_ty) in
      let tl = if tl = [] then List.map mkt pl else tl in
      let rl = List.map (fun pl -> pl, ()) ppl in
      let mk_case _ _ = () and mk_let _ _ _ = () in
      compile ~get_constructors ~mk_case ~mk_let false false tl rl *)

let is_exhaustive tl = function
  | [] -> false
  | (pl::_) as ppl ->
      let mkt p = t_var (create_vsymbol (id_fresh "_") p.pat_ty) in
      let tl = if tl = [] then List.map mkt pl else tl in
      let rl = List.map (fun pl -> pl, true) ppl in
      let get_constructors _ = [] in
      let mk_case _ _ = true and mk_let _ _ _ = true in
      try compile ~get_constructors ~mk_case ~mk_let true false tl rl
      with NonExhaustive _ -> false
