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

open Wstdlib
open Ident
open Ty
open Term

let sexp_of_ind_sign (x: ind_sign) : Sexplib0.Sexp.t =
  match x with Ind -> Sexplib0.Sexp.Atom "Ind" | Coind -> Sexplib0.Sexp.Atom "Coind"

let ind_sign_of_sexp (x: Sexplib0.Sexp.t) : ind_sign =
  match x with
  | Sexplib0.Sexp.Atom "Ind" -> Ind
  | Sexplib0.Sexp.Atom "Coind"  -> Coind 
  | _ -> Sexplib0.Sexp_conv.of_sexp_error "ind_sign_of_sexp" x 


let sexp_of_prop_kind (x: prop_kind) : Sexplib0.Sexp.t =
   match x with Plemma -> Sexplib0.Sexp.Atom "Plemma" | Paxiom -> Sexplib0.Sexp.Atom "Paxiom" | Pgoal -> Sexplib0.Sexp.Atom "Pgoal"


let prop_kind_of_sexp (x: Sexplib0.Sexp.t) : prop_kind =
  match x with
  | Sexplib0.Sexp.Atom "Plemma" -> Plemma
  | Sexplib0.Sexp.Atom "Paxiom"  -> Paxiom 
  | Sexplib0.Sexp.Atom "Pgoal"  -> Pgoal 
  | _ -> Sexplib0.Sexp_conv.of_sexp_error "prop_kind_of_sexp" x 

(*  (*Type declaration*)

type constructor = lsymbol * lsymbol option list
(** constructor symbol with the list of projections *)

type data_decl = tysymbol * constructor list

(** Logic declaration *)

type ls_defn = lsymbol * term * int list

type logic_decl = lsymbol * ls_defn

exception UnboundVar of vsymbol
exception UnexpectedProjOrConstr of lsymbol

let check_fvs f =
  t_v_fold (fun _ vs -> raise (UnboundVar vs)) () f;
  t_prop f

let check_vl ty v = ty_equal_check ty v.vs_ty*)
let check_tl ty t = ty_equal_check ty (t_type t)

(*let make_ls_defn ls vl t =
  (* check ls *)
  if not (BigInt.is_zero ls.ls_constr) || ls.ls_proj then raise (UnexpectedProjOrConstr ls);
  (* check for duplicate arguments *)
  let add_v s v = Svs.add_new (DuplicateVar v) v s in
  ignore (List.fold_left add_v Svs.empty vl);
  (* build the definition axiom *)
  let hd = t_app ls (List.map t_var vl) t.t_ty in
  let bd = TermTF.t_selecti t_equ t_iff hd t in
  let fd = check_fvs (t_forall_close vl [] bd) in
  (* check for unbound type variables *)
  let htv = t_ty_freevars Stv.empty hd in
  let ttv = t_ty_freevars Stv.empty t in
  if not (Stv.subset ttv htv) then
    raise (UnboundTypeVar (Stv.choose (Stv.diff ttv htv)));
  (* check correspondence with the type signature of ls *)
  List.iter2 check_vl ls.ls_args vl;
  t_ty_check t ls.ls_value;
  (* return the definition *)
  ls, (ls, fd, []) *)

(*JOSH - TODO hack*)
(* let make_ls_defn ls vl t =
  let l, ((l1, t), l2) = make_ls_defn ls vl t in
  l, (l1, t, l2) *)

let open_ls_defn ((_,f),_) =
  let vl,_,f = match f.t_node with
    | Tquant (Tforall,b) -> t_open_quant b
    | _ -> [],[],f in
  match f.t_node with
    | Tapp (_, [_; f])
    | Tbinop (_, _, f) -> vl,f
    | _ -> assert false

let open_ls_defn_cb ld =
  let (ls,_),_ = ld in
  let vl,t = open_ls_defn ld in
  let close ls' vl' t' =
    if t_equal_strict t t' && Lists.equal vs_equal vl vl' && ls_equal ls ls'
    then ls,ld else make_ls_defn ls' vl' t'
  in
  vl,t,close

let ls_defn_decrease ((_,_),l) = l

let ls_defn_axiom ((_,f),_) = f

let ls_defn_of_axiom f =
  let _,_,f = match f.t_node with
    | Tquant (Tforall,b) -> t_open_quant b
    | _ -> [],[],f in
  let hd,e = match f.t_node with
    | Tapp (ls, [hd; t]) when ls_equal ls ps_equ -> hd,t
    | Tbinop (Tiff, hd, f) -> hd,f
    | _ -> raise Exit in
  let ls,tl = match hd.t_node with
    | Tapp (ls,tl) -> ls,tl
    | _ -> raise Exit in
  let vs_of_t t = match t.t_node with
    | Tvar v -> v
    | _ -> raise Exit in
  let vl = List.map vs_of_t tl in
  make_ls_defn ls vl e

let ls_defn_of_axiom f =
  try Some (ls_defn_of_axiom f) with
    | Exit | UnboundVar _ | UnboundTypeVar _
    | DuplicateVar _ | TypeMismatch _ | UnexpectedProjOrConstr _ -> None

(** Termination checking for mutually recursive logic declarations *)

type descent =
  | Less of int
  | Equal of int
  | Unknown

type call_set = (ident * descent array) Hid.t
type vs_graph = descent Mvs.t list

let create_call_set () = Hid.create 5

let create_vs_graph vl =
  let i = ref (-1) in
  let add vm v = incr i; Mvs.add v (Equal !i) vm in
  [List.fold_left add Mvs.empty vl]

(* TODO: can we handle projections somehow? *)
let register_call cgr caller vsg callee tl =
  let call vm =
    let describe t = match t.t_node with
      | Tvar v -> Mvs.find_def Unknown v vm
      | _ -> Unknown in
    let dl = List.map describe tl in
    Hid.add cgr callee (caller, Array.of_list dl) in
  List.iter call vsg

let vs_graph_drop vsg u = List.rev_map (Mvs.remove u) vsg

(* TODO: can we handle projections somehow? *)
let vs_graph_let vsg t u = match t.t_node with
  | Tvar v ->
      let add vm = try Mvs.add u (Mvs.find v vm) vm
                  with Not_found -> Mvs.remove u vm in
      List.rev_map add vsg
  | _ ->
      vs_graph_drop vsg u

let rec match_var link acc p = match p.pat_node with
  | Pwild -> acc
  | Pvar u -> List.rev_map (Mvs.add u link) acc
  | Pas (p,u) -> List.rev_map (Mvs.add u link) (match_var link acc p)
  | Por (p1,p2) ->
      List.rev_append (match_var link acc p1) (match_var link acc p2)
  | Papp _ ->
      let link = match link with
        | Unknown -> Unknown
        | Equal i -> Less i
        | Less i  -> Less i in
      let join u = Mvs.add u link in
      List.rev_map (Svs.fold join p.pat_vars) acc

let rec match_term vm t acc p = match t.t_node, p.pat_node with
  | _, Pwild -> acc
  | Tvar v, _ when Mvs.mem v vm ->
      match_var (Mvs.find v vm) acc p
  | Tapp _, Pvar u ->
      vs_graph_drop acc u
  | Tapp _, Pas (p,u) ->
      match_term vm t (vs_graph_drop acc u) p
  | Tapp _, Por (p1,p2) ->
      List.rev_append (match_term vm t acc p1) (match_term vm t acc p2)
  | Tapp (c1,tl), Papp (c2,pl) when ls_equal c1 c2 ->
      let down l t p = match_term vm t l p in
      List.fold_left2 down acc tl pl
  | _,_ ->
      List.rev_map (fun vm -> Mvs.set_diff vm p.pat_vars) acc

let vs_graph_pat vsg t p =
  let add acc vm = List.rev_append (match_term vm t [vm] p) acc in
  List.fold_left add [] vsg

let build_call_graph cgr syms ls (vl,e) =
  let rec term vm () t = match t.t_node with
    | Tapp (s,tl) when Mls.mem s syms ->
        t_fold (term vm) () t;
        register_call cgr ls.ls_name vm s.ls_name tl
    | Tlet (t,b) ->
        term vm () t;
        let u,e = t_open_bound b in
        term (vs_graph_let vm t u) () e
    | Tcase (t,bl) ->
        term vm () t;
        List.iter (fun b ->
          let p,e = t_open_branch b in
          term (vs_graph_pat vm t p) () e) bl
    | Tquant (_,b) -> (* ignore triggers *)
        let _,_,f = t_open_quant b in term vm () f
    | _ ->
        t_fold (term vm) () t
  in
  term (create_vs_graph vl) () e

let build_call_list cgr id =
  let htb = Hid.create 5 in
  let local v = Array.mapi (fun i -> function
    | (Less j) as d when i = j -> d
    | (Equal j) as d when i = j -> d
    | _ -> Unknown) v
  in
  let subsumes v1 v2 =
    let sbs d1 d2 = match d1,d2 with
      | _, Unknown -> ()
      | Equal u1, Equal u2 when u1 = u2 -> ()
      | Less  u1, Equal u2 when u1 = u2 -> ()
      | Less  u1, Less  u2 when u1 = u2 -> ()
      | _,_ -> raise Not_found
    in
    let test i d1 = sbs d1 (Array.get v2 i) in
    try Array.iteri test v1; true with Not_found -> false
  in
  let subsumed s c =
    List.exists (subsumes c) (Hid.find_all htb s)
  in
  let multiply v1 v2 =
    let to_less = function
      | Unknown -> Unknown
      | Equal i -> Less i
      | Less i  -> Less i
    in
    Array.map (function
      | Unknown -> Unknown
      | Equal i -> Array.get v2 i
      | Less i -> to_less (Array.get v2 i)) v1
  in
  let resolve s c =
    Hid.add htb s c;
    let mult (s,v) = (s, multiply c v) in
    List.rev_map mult (Hid.find_all cgr s)
  in
  let rec add_call lc = function
    | [] -> lc
    | (s,c)::r when id_equal id s -> add_call (local c :: lc) r
    | (s,c)::r when subsumed s c -> add_call lc r
    | (s,c)::r -> add_call lc (List.rev_append (resolve s c) r)
  in
  add_call [] (Hid.find_all cgr id)

let find_variant exn cgr id =
  let cl = build_call_list cgr id in
  let add d1 d2 = match d1, d2 with
    | Unknown, _ -> d1
    | _, Unknown -> d2
    | Less _, _  -> d1
    | _, Less _  -> d2
    | _, _ -> d1
  in
  let add v1 v2 =
    Array.mapi (fun i d1 -> add d1 (Array.get v2 i)) v1
  in
  let rec check acc mx = match mx with
    | [] -> List.rev acc
    | a :: r ->
        (* calculate the bitwise minimum of all call vectors *)
        let p = List.fold_left add a r in
        (* find the decreasing argument positions *)
        let find l = function Less i -> i :: l | _ -> l in
        let res = Array.fold_left find [] p in
        (* eliminate the decreasing calls *)
        if res = [] then raise exn;
        let test a =
          List.for_all (fun i -> Array.get a i <> Less i) res
        in
        check (List.rev_append res acc) (List.filter test mx)
  in
  check [] cl

exception NoTerminationProof of lsymbol

let check_termination ldl =
  let cgr = create_call_set () in
  let add acc (ls,ld) = Mls.add ls (open_ls_defn ld) acc in
  let syms = List.fold_left add Mls.empty ldl in
  Mls.iter (build_call_graph cgr syms) syms;
  let check ls _ =
    find_variant (NoTerminationProof ls) cgr ls.ls_name in
  let res = Mls.mapi check syms in
  List.map (fun (ls,((_,f),_)) -> (ls,((ls,f),Mls.find ls res))) ldl 

(** Inductive predicate declaration *)

(* type prsymbol = {
  pr_name : ident;
} *)

module Prop = MakeMSHW (struct
  type t = prsymbol
  let tag pr = pr.pr_name.id_tag
  let equal = (==) (*JOSH TODO equal*)
end)

module Spr = Prop.S
module Mpr = Prop.M
module Hpr = Prop.H
module Wpr = Prop.W

let pr_equal : prsymbol -> prsymbol -> bool = (==)

let pr_hash pr = id_hash pr.pr_name

let create_prsymbol n = { pr_name = id_register n }

(* type ind_decl = lsymbol * (prsymbol * term) list *)

(* type ind_sign = Ind | Coind
[@@deriving sexp]

type ind_list = ind_sign * ind_decl list *)

(** Proposition declaration *)

(* type prop_kind =
  | Plemma    (* prove, use as a premise *)
  | Paxiom    (* do not prove, use as a premise *)
  | Pgoal     (* prove, do not use as a premise *)
[@@deriving sexp]

type prop_decl = prop_kind * prsymbol * term *)

(** Declaration type *)

(*type decl = {
  d_node : decl_node;
  d_news : Sid.t;         (* idents introduced in declaration *)
  d_tag  : Weakhtbl.tag;  (* unique magical tag *)
}

and decl_node =
  | Dtype  of tysymbol          (* abstract types and aliases *)
  | Ddata  of data_decl list    (* recursive algebraic types *)
  | Dparam of lsymbol           (* abstract functions and predicates *)
  | Dlogic of logic_decl list   (* recursive functions and predicates *)
  | Dind   of ind_list          (* (co)inductive predicates *)
  | Dprop  of prop_decl         (* axiom / lemma / goal *)
*)
(** Declarations *)

module Hsdecl = Hashcons.Make (struct

  type t = decl

  let cs_equal (cs1,pl1) (cs2,pl2) =
    ls_equal cs1 cs2 && Lists.equal (Option.equal ls_equal) pl1 pl2

  let eq_td (ts1,td1) (ts2,td2) =
    ts_equal ts1 ts2 && Lists.equal cs_equal td1 td2

  let eq_ld (ls1,((_,f1),_)) (ls2,((_,f2),_)) =
    ls_equal ls1 ls2 && t_equal_strict f1 f2

  let eq_iax (pr1,fr1) (pr2,fr2) =
    pr_equal pr1 pr2 && t_equal_strict fr1 fr2

  let eq_ind (ps1,al1) (ps2,al2) =
    ls_equal ps1 ps2 && Lists.equal eq_iax al1 al2

  let equal d1 d2 = match d1.d_node, d2.d_node with
    | Dtype  s1, Dtype  s2 -> ts_equal s1 s2
    | Ddata  l1, Ddata  l2 -> Lists.equal eq_td l1 l2
    | Dparam s1, Dparam s2 -> ls_equal s1 s2
    | Dlogic l1, Dlogic l2 -> Lists.equal eq_ld l1 l2
    | Dind   (s1,l1), Dind (s2,l2) -> s1 = s2 && Lists.equal eq_ind l1 l2
    | Dprop (k1,pr1,f1), Dprop (k2,pr2,f2) ->
        k1 = k2 && pr_equal pr1 pr2 && t_equal_strict f1 f2
    | _,_ -> false

  let cs_hash (cs,pl) =
    (Hashcons.combine_big_list (Hashcons.combine_big_option ls_hash) (ls_hash cs) pl) 

  let hs_td (ts,td) = Hashcons.combine_big_list cs_hash (ts_hash ts) td

  let hs_ld (ls,((_,f),_)) = Hashcons.combine_big (ls_hash ls) (t_hash_strict f)

  let hs_prop (pr,f) = Hashcons.combine_big (pr_hash pr)(t_hash_strict f)

  let hs_ind (ps,al) = Hashcons.combine_big_list hs_prop (ls_hash ps) al

  let hs_kind = function
    | Plemma -> BigInt.of_int 11 | Paxiom -> BigInt.of_int 13 | Pgoal -> BigInt.of_int 17

  let hash d =  (match d.d_node with
    | Dtype  s -> ts_hash s
    | Ddata  l -> Hashcons.combine_big_list hs_td (BigInt.of_int 3) l
    | Dparam s -> ls_hash s
    | Dlogic l -> Hashcons.combine_big_list hs_ld (BigInt.of_int 5) l
    | Dind (_,l) -> Hashcons.combine_big_list hs_ind (BigInt.of_int 7) l
    | Dprop (k,pr,f) -> Hashcons.combine_big (hs_kind k) (hs_prop (pr,f)))

  let tag n d = { d with d_tag = Weakhtbl.create_tag n }

end)

module Decl = MakeMSHW (struct
  type t = decl
  let tag d = d.d_tag
  let equal = (==) (*JOSH TODO equal*)
end)

module Sdecl = Decl.S
module Mdecl = Decl.M
module Wdecl = Decl.W
module Hdecl = Decl.H

let d_equal : decl -> decl -> bool = (==)

let d_hash d = Weakhtbl.tag_hash d.d_tag

(** Declaration constructors *)

let mk_decl node news =
  let d = {
      d_node = node;
      d_news = news;
      d_tag  = Weakhtbl.dummy_tag;
    } in
  match node with
  | Dprop (Pgoal,_,_) -> Hsdecl.unique d
  | _ -> Hsdecl.hashcons d


exception IllegalTypeAlias of tysymbol
exception ClashIdent of ident
exception BadLogicDecl of lsymbol * lsymbol
exception BadConstructor of lsymbol

exception BadRecordField of lsymbol
exception BadRecordType of lsymbol * tysymbol
exception BadRecordUnnamed of lsymbol * tysymbol
exception BadRecordCons of lsymbol * tysymbol
exception RecordFieldMissing of lsymbol
exception DuplicateRecordField of lsymbol

exception EmptyDecl
exception EmptyAlgDecl of tysymbol
exception EmptyIndDecl of lsymbol

exception NonPositiveTypeDecl of tysymbol * lsymbol * ty

let news_id s id = Sid.add_new (ClashIdent id) id s

let syms_ts s ts = Sid.add ts.ts_name s
let syms_ls s ls = Sid.add ls.ls_name s

let syms_ty s ty = ty_s_fold syms_ts s ty
let syms_term s t = t_s_fold syms_ty syms_ls s t

let syms_ty_decl ts =
  type_def_fold syms_ty Sid.empty ts.ts_def

let create_ty_decl ts =
  let news = Sid.singleton ts.ts_name in
  mk_decl (Dtype ts) news

let syms_data_decl tdl =
  let syms_constr syms (fs,_) =
    List.fold_left syms_ty syms fs.ls_args in
  let syms_decl syms (_,cl) =
    List.fold_left syms_constr syms cl in
  List.fold_left syms_decl Sid.empty tdl

let create_data_decl tdl =
  if tdl = [] then raise EmptyDecl;
  let add s (ts,_) = Sts.add ts s in
  let tss = List.fold_left add Sts.empty tdl in
  let check_proj tyv s tya ls = match ls with
    | None -> s
    | Some ({ls_args = [ptyv]; ls_value = Some ptya; ls_constr = b; ls_proj=true} as ls) ->
        if BigInt.is_zero b then
        (ty_equal_check tyv ptyv;
        ty_equal_check tya ptya;
        Sls.add_new (DuplicateRecordField ls) ls s)
        else raise (BadRecordField ls)
    | Some ls -> raise (BadRecordField ls)
  in
  let check_constr tys ty cll pjs news (fs,pl) =
    ty_equal_check ty (Opt.get_exn (BadConstructor fs) fs.ls_value);
    let fs_pjs =
      try List.fold_left2 (check_proj ty) Sls.empty fs.ls_args pl
      with Invalid_argument _ -> raise (BadConstructor fs) in
    if not (Sls.equal pjs fs_pjs) then
      raise (RecordFieldMissing (Sls.choose (Sls.diff pjs fs_pjs)));
    if not (BigInt.eq fs.ls_constr cll) then raise (BadConstructor fs);
    let vs = ty_freevars Stv.empty ty in
    let rec check seen ty = match ty.ty_node with
      | Tyvar v when Stv.mem v vs -> ()
      | Tyvar v -> raise (UnboundTypeVar v)
      | Tyapp (ts,tl) ->
          let now = Sts.mem ts tss in
          if seen && now
            then raise (NonPositiveTypeDecl (tys,fs,ty))
            else List.iter (check (seen || now)) tl
    in
    List.iter (check false) fs.ls_args;
    news_id news fs.ls_name
  in
  let check_decl news (ts,cl) =
    let cll = BigInt.of_int (List.length cl) in
    if cl = [] then raise (EmptyAlgDecl ts);
    if ts.ts_def <> NoDef then raise (IllegalTypeAlias ts);
    let news = news_id news ts.ts_name in
    let pjs = List.fold_left (fun s (_,pl) ->
      List.fold_left (Opt.fold Sls.add_left) s pl) Sls.empty cl in
    let news = Sls.fold (fun pj s -> news_id s pj.ls_name) pjs news in
    let ty = ty_app ts (List.map ty_var ts.ts_args) in
    List.fold_left (check_constr ts ty cll pjs) news cl
  in
  let news = List.fold_left check_decl Sid.empty tdl in
  mk_decl (Ddata tdl) news

let syms_param_decl ls =
  let syms = Opt.fold syms_ty Sid.empty ls.ls_value in
  List.fold_left syms_ty syms ls.ls_args

let create_param_decl ls =
  if not (BigInt.is_zero ls.ls_constr) || ls.ls_proj then raise (UnexpectedProjOrConstr ls);
  let news = Sid.singleton ls.ls_name in
  mk_decl (Dparam ls) news

let syms_logic_decl ldl =
  let syms_decl syms (ls,ld) =
    let _, e = open_ls_defn ld in
    let syms = List.fold_left syms_ty syms ls.ls_args in
    syms_term syms e
  in
  List.fold_left syms_decl Sid.empty ldl

(*JOSH: TODO hack*)
let lsym_ocaml_to_coq (x, (y, z, w)) =
  (x, ((y, z), w))

let create_logic_decl ldl =
  if ldl = [] then raise EmptyDecl;
  let check_decl news (ls,((s,_),_)) =
    if not (ls_equal s ls) then raise (BadLogicDecl (ls, s));
    if not (BigInt.is_zero ls.ls_constr) || ls.ls_proj then raise (UnexpectedProjOrConstr ls);
    news_id news ls.ls_name
  in
  let news = List.fold_left check_decl Sid.empty ldl in
  let ldl = check_termination ldl in
  (*JOSH: TODO hack*)
  (* let ldl = List.map lsym_ocaml_to_coq ldl in *)
  mk_decl (Dlogic ldl) news

exception InvalidIndDecl of lsymbol * prsymbol
exception NonPositiveIndDecl of lsymbol * prsymbol * lsymbol

exception Found of lsymbol
let ls_mem s sps = if Sls.mem s sps then raise (Found s) else false
let t_pos_ps sps = t_s_all (fun _ -> true) (fun s -> not (ls_mem s sps))

let rec f_pos_ps sps pol f = match f.t_node, pol with
  | Tapp (s, _), Some false when ls_mem s sps -> false
  | Tapp (s, _), None when ls_mem s sps -> false
  | Tbinop (Tiff, f, g), _ ->
      f_pos_ps sps None f && f_pos_ps sps None g
  | Tbinop (Timplies, f, g), _ ->
      f_pos_ps sps (Option.map not pol) f && f_pos_ps sps pol g
  | Tnot f, _ ->
      f_pos_ps sps (Option.map not pol) f
  | Tif (f,g,h), _ ->
      f_pos_ps sps None f && f_pos_ps sps pol g && f_pos_ps sps pol h
  | _ -> TermTF.t_all (t_pos_ps sps) (f_pos_ps sps pol) f

let syms_ind_decl idl =
  let syms_ax syms (_,f) =
    syms_term syms f in
  let syms_decl syms (_,al) =
    List.fold_left syms_ax syms al in
  List.fold_left syms_decl Sid.empty idl

let create_ind_decl s idl =
  if idl = [] then raise EmptyDecl;
  let add acc (ps,_) = Sls.add ps acc in
  let sps = List.fold_left add Sls.empty idl in
  let check_ax ps news (pr,f) =
    let rec clause acc f = match f.t_node with
      | Tquant (Tforall, f) ->
          let _,_,f = t_open_quant f in clause acc f
      | Tbinop (Timplies, g, f) -> clause (g::acc) f
      | Tlet (t, bf) ->
          let v, f = t_open_bound bf in
          clause (t_equ (t_var v) t :: acc) f
      | _ -> (acc, f)
    in
    let cls, g = clause [] (check_fvs f) in
    match g.t_node with
      | Tapp (s, tl) when ls_equal s ps ->
          List.iter2 check_tl ps.ls_args tl;
          (try ignore (List.for_all (f_pos_ps sps (Some true)) (g::cls))
          with Found ls -> raise (NonPositiveIndDecl (ps, pr, ls)));
          (* check for unbound type variables *)
          let gtv = t_ty_freevars Stv.empty g in
          let ftv = t_ty_freevars Stv.empty f in
          if not (Stv.subset ftv gtv) then
            raise (UnboundTypeVar (Stv.choose (Stv.diff ftv gtv)));
          news_id news pr.pr_name
      | _ -> raise (InvalidIndDecl (ps, pr))
  in
  let check_decl news (ps,al) =
    if al = [] then raise (EmptyIndDecl ps);
    if ps.ls_value <> None then raise (Term.PredicateSymbolExpected ps);
    let news = news_id news ps.ls_name in
    List.fold_left (check_ax ps) news al
  in
  let news = List.fold_left check_decl Sid.empty idl in
  mk_decl (Dind (s, idl)) news

let syms_prop_decl f =
  syms_term Sid.empty f

let create_prop_decl k p f =
  let news = news_id Sid.empty p.pr_name in
  mk_decl (Dprop (k,p,check_fvs f)) news

let get_used_syms_ty ty = syms_ty Sid.empty ty

let get_used_syms_decl d =
  match d.d_node with
  | Dtype ts -> syms_ty_decl ts
  | Ddata dl -> syms_data_decl dl
  | Dparam ls -> syms_param_decl ls
  | Dlogic ldl -> syms_logic_decl ldl
  | Dind (_, idl) -> syms_ind_decl idl
  | Dprop (_,_,f) -> syms_prop_decl f

(** Utilities *)

let decl_map fn d = match d.d_node with
  | Dtype _ | Ddata _ | Dparam _ -> d
  | Dlogic l ->
      let fn (ls,ld) =
        let vl,e,close = open_ls_defn_cb ld in
        close ls vl (fn e)
      in
      create_logic_decl (List.map fn l)
  | Dind (s, l) ->
      let fn (pr,f) = pr, fn f in
      let fn (ps,l) = ps, List.map fn l in
      create_ind_decl s (List.map fn l)
  | Dprop (k,pr,f) ->
      create_prop_decl k pr (fn f)

let decl_fold fn acc d = match d.d_node with
  | Dtype _ | Ddata _ | Dparam _ -> acc
  | Dlogic l ->
      let fn acc (_,ld) =
        let _,e = open_ls_defn ld in
        fn acc e
      in
      List.fold_left fn acc l
  | Dind (_, l) ->
      let fn acc (_,f) = fn acc f in
      let fn acc (_,l) = List.fold_left fn acc l in
      List.fold_left fn acc l
  | Dprop (_,_,f) ->
      fn acc f

let list_rpair_map_fold fn =
  let fn acc (x1,x2) =
    let acc,x2 = fn acc x2 in acc,(x1,x2) in
  Lists.map_fold_left fn

let decl_map_fold fn acc d = match d.d_node with
  | Dtype _ | Ddata _ | Dparam _ -> acc, d
  | Dlogic l ->
      let fn acc (ls,ld) =
        let vl,e,close = open_ls_defn_cb ld in
        let acc,e = fn acc e in
        acc, close ls vl e
      in
      let acc,l = Lists.map_fold_left fn acc l in
      acc, create_logic_decl l
  | Dind (s, l) ->
      let acc, l = list_rpair_map_fold (list_rpair_map_fold fn) acc l in
      acc, create_ind_decl s l
  | Dprop (k,pr,f) ->
      let acc, f = fn acc f in
      acc, create_prop_decl k pr f

module DeclTF = struct
  let decl_map fnT fnF = decl_map (TermTF.t_select fnT fnF)
  let decl_fold fnT fnF = decl_fold (TermTF.t_selecti fnT fnF)
  let decl_map_fold fnT fnF = decl_map_fold (TermTF.t_selecti fnT fnF)
end

(** Known identifiers *)

exception KnownIdent of ident
exception UnknownIdent of ident
exception RedeclaredIdent of ident

type known_map = decl Mid.t

let known_id kn id =
  if not (Mid.mem id kn) then raise (UnknownIdent id)

let merge_known kn1 kn2 =
  let check_known id decl1 decl2 =
    if d_equal decl1 decl2 then Some decl1
    else raise (RedeclaredIdent id)
  in
  Mid.union check_known kn1 kn2

let known_add_decl kn0 decl =
  let kn = Mid.map (Util.const decl) decl.d_news in
  let check id decl0 _ =
    if d_equal decl0 decl
    then raise (KnownIdent id)
    else raise (RedeclaredIdent id)
  in
  let kn = Mid.union check kn0 kn in
  let unk = Mid.set_diff (get_used_syms_decl decl) kn in
  if Sid.is_empty unk then kn
  else raise (UnknownIdent (Sid.choose unk))

let find_constructors kn ts =
  match (Mid.find ts.ts_name kn).d_node with
  | Dtype _ -> []
  | Ddata dl -> List.assq ts dl
  | Dparam _ | Dlogic _ | Dind _ | Dprop _ -> assert false

let find_inductive_cases kn ps =
  match (Mid.find ps.ls_name kn).d_node with
  | Dind (_, dl) -> List.assq ps dl
  | Dlogic _ | Dparam _ | Ddata _ -> []
  | Dtype _ | Dprop _ -> assert false

let find_logic_definition kn ls =
  match (Mid.find ls.ls_name kn).d_node with
  | Dlogic dl -> Some (List.assq ls dl)
  | Dparam _ | Dind _ | Ddata _ -> None
  | Dtype _ | Dprop _ -> assert false

let find_prop kn pr =
  match (Mid.find pr.pr_name kn).d_node with
  | Dind (_, dl) ->
      let test (_,l) = List.mem_assq pr l in
      List.assq pr (snd (List.find test dl))
  | Dprop (_,_,f) -> f
  | Dtype _ | Ddata _ | Dparam _ | Dlogic _ -> assert false

let find_prop_decl kn pr =
  match (Mid.find pr.pr_name kn).d_node with
  | Dind (_, dl) ->
      let test (_,l) = List.mem_assq pr l in
      Paxiom, List.assq pr (snd (List.find test dl))
  | Dprop (k,_,f) -> k,f
  | Dtype _ | Ddata _ | Dparam _ | Dlogic _ -> assert false

let check_match kn d =
  let rec check () t = match t.t_node with
    | Tcase (t1,bl) ->
        let get_constructors ts = List.map fst (find_constructors kn ts) in
        let pl = List.map (fun b -> let p,_ = t_open_branch b in [p]) bl in
        Loc.try2 ?loc:t.t_loc (Pattern.check_compile ~get_constructors) [t1] pl;
        t_fold check () t
    | _ -> t_fold check () t
  in
  decl_fold check () d

exception NonFoundedTypeDecl of tysymbol

let check_foundness kn d =
  let rec check_ts tss tvs ts =
    (* recursive data type, abandon *)
    if Sts.mem ts tss then false else
    let cl = find_constructors kn ts in
    (* an abstract type is inhabited iff
       all its type arguments are inhabited *)
    if cl == [] then Stv.is_empty tvs else
    (* an algebraic type is inhabited iff
       we can build a value of this type *)
    let tss = Sts.add ts tss in
    List.exists (check_constr tss tvs) cl
  and check_constr tss tvs (ls,_) =
    (* we can construct a value iff every
       argument is of an inhabited type *)
    List.for_all (check_type tss tvs) ls.ls_args
  and check_type tss tvs ty = match ty.ty_node with
    | Tyvar tv ->
        not (Stv.mem tv tvs)
    | Tyapp (ts,tl) ->
        let check acc tv ty =
          if check_type tss tvs ty then acc else Stv.add tv acc in
        let tvs = List.fold_left2 check Stv.empty ts.ts_args tl in
        check_ts tss tvs ts
  in
  match d.d_node with
  | Ddata tdl ->
      let check () (ts,_) =
        if check_ts Sts.empty Stv.empty ts
        then () else raise (NonFoundedTypeDecl ts)
      in
      List.fold_left check () tdl
  | _ -> ()

let rec ts_extract_pos kn sts ts =
  assert (not (is_alias_type_def ts.ts_def));
  if ts_equal ts ts_func then [false;true] else
  if Sts.mem ts sts then List.map Util.ttrue ts.ts_args else
  match find_constructors kn ts with
    | [] ->
        List.map Util.ffalse ts.ts_args
    | csl ->
        let sts = Sts.add ts sts in
        let rec get_ty stv ty = match ty.ty_node with
          | Tyvar _ -> stv
          | Tyapp (ts,tl) ->
              let get acc pos =
                if pos then get_ty acc else ty_freevars acc in
              List.fold_left2 get stv (ts_extract_pos kn sts ts) tl
        in
        let get_cs acc (ls,_) = List.fold_left get_ty acc ls.ls_args in
        let negs = List.fold_left get_cs Stv.empty csl in
        List.map (fun v -> not (Stv.mem v negs)) ts.ts_args

let check_positivity kn d = match d.d_node with
  | Ddata tdl ->
      let add s (ts,_) = Sts.add ts s in
      let tss = List.fold_left add Sts.empty tdl in
      let check_constr tys (cs,_) =
        let rec check_ty ty = match ty.ty_node with
          | Tyvar _ -> ()
          | Tyapp (ts,tl) ->
              let check pos ty =
                if pos then check_ty ty else
                if ty_s_any (Sts.contains tss) ty then
                  raise (NonPositiveTypeDecl (tys,cs,ty)) in
              List.iter2 check (ts_extract_pos kn Sts.empty ts) tl
        in
        List.iter check_ty cs.ls_args
      in
      let check_decl (ts,cl) = List.iter (check_constr ts) cl in
      List.iter check_decl tdl
  | _ -> ()

(*JOSH - HERE, we will add termination check.
 Unlike Why3, our termination check depends on type definitions*)

(*TODO: is this defined?*)
let null (l: 'a list) : bool = 
  match l with
  | [] -> true
  | _ -> false

(*TODO?*)
(* type mut_adt = data_decl list
type mut_info = mut_adt list *  mut_adt Mts.t *)

(*TODO: move*)
(*Get all mutual ADT definitions:
gives set of mutual adts and map adt name -> mut_adt*)
(* let get_ctx_tys (kn: decl Mid.t) : mut_info  =
  Mid.fold (fun _ d acc ->
    match d.d_node with
    | Ddata m ->
      let (ms, mp) = acc in
      (m :: ms, List.fold_right (fun t ts -> Mts.add t m ts) (List.map fst m) mp )
    | _ -> acc) kn ([], Mts.empty) *)

(*TODO: move I think*)
(*let is_vty_adt (ctx: mut_info) (t: ty) : (mut_adt * tysymbol * ty list) option =
  match t.ty_node with
  | Tyapp (ts, tys) -> Option.bind (Mts.find_opt ts (snd ctx)) (fun m -> Some (m, ts, tys))
  | Tyvar _ -> None

let ts_in_mut (ts: tysymbol) (m: mut_adt) : bool =
  match List.find_opt (fun a -> (fst a) = ts) m with | Some _ -> true | None -> false

let vty_in_m (m: mut_adt) (vs: ty list) (v: ty) : bool =
  match v.ty_node with
  | Tyapp(ts, vs') -> ts_in_mut ts m && List.equal ty_equal vs vs'
  | _ -> false

let vty_in_m' (m: mut_adt) (v: ty) : bool =
  match v.ty_node with
  | Tyapp(ts, vs') -> ts_in_mut ts m
  | _ -> false*)

(*Create map of [mut_adt * ty list]*)

(*Need way to create tag of tuple*)

(*A hack - should really use maps but it is complicated with
  tuples and lists - are BSTs the way to go?*)
(*Inefficient of course*)
(* let add_union (eq: 'a -> 'a -> bool) (x: 'a) (l: 'a list) =
  if List.exists (fun y -> eq x y) l then l else x :: l


let get_adts_present (ctx: mut_info) (l: vsymbol list) : (mut_adt * ty list) list =
  List.fold_right (fun v acc -> 
    match (is_vty_adt ctx v.vs_ty) with
    | Some ((m, a), vs) -> add_union (=) (m, vs) acc
    | None -> acc
    ) l [] *)
(*TEMP - change to bigint*)
(*NOTE: from 0 to n-1, NOT 1 to n - NEEDS to be increasing order*)
(*TODO: include in IntFuncs*)
(*iota is from 1 to n, we want 0 to n-1*)
(*let iota2 (n: BigInt.t) : BigInt.t list =
  List.rev(List.map BigInt.pred (IntFuncs.iota n))*)
(* let iota (n: BigInt.t) : BigInt.t list =
  let rec iota_aux n = 
  if BigInt.lt n BigInt.zero
    then []
    else if BigInt.is_zero n then [] else BigInt.pred n :: (iota_aux (BigInt.pred n)) in
  List.rev (iota_aux n) *)

(*TODO: combine probably*)
(* let get_idx_lists_aux kn (funs: (vsymbol list * term) Mls.t) :  (data_decl list * ty list * (BigInt.t list) list) list =
    let syms : vsymbol list list = Mls.fold (fun _ x y -> (fst x) :: y) funs [] in
    List.map (fun (m, vs) -> 
    
      let l : BigInt.t list list =
        List.map (fun args ->
          List.map fst (List.filter (fun it -> vty_in_m m vs (snd it)) 
            (List.combine (iota2 (IntFuncs.int_length args)) (List.map (fun v -> v.vs_ty) args)))

        ) syms
        in
        (*If any are null, discard*)
        (m, vs, if List.exists null l then [] else l)
      
    ) 
    (get_adts_present (get_ctx_tys kn) (List.concat syms))


let get_idx_lists kn (funs: (vsymbol list * term) Mls.t) : (data_decl list * ty list * (BigInt.t list) list) list =
  List.filter (fun (_, _, x) -> not (null x)) (get_idx_lists_aux kn funs) *)

(* let rec get_possible_index_lists (l: BigInt.t list list) : BigInt.t list list =
  match l with
  | l1 :: rest -> let r = get_possible_index_lists rest in
    List.concat (List.map (fun x -> List.map (fun y -> x :: y) r) l1)
  | [] -> [[]] *)

(*The core of the termination checking (TODO move?)*)

(* let check_unif_map (m: ty Mtv.t) : bool =
  Mtv.for_all (fun (v: tvsymbol) (t : ty) -> 
    match t.ty_node with 
      | Tyvar v1 -> tv_equal v v1 
      | _ -> false
      ) m *)

(* let check_inst_eq (m: ty Mtv.t) (syms: tvsymbol list) (tys: ty list) : bool =
  List.for_all (fun (v, t) -> match Mtv.find_opt v m with | Some t1 -> ty_equal t t1 | None -> false) 
    (List.combine syms tys) *)

(* let vsym_in_m (m: mut_adt) (vs: ty list) (x: vsymbol) : bool =
  vty_in_m m vs (x.vs_ty)

let constr_in_m (l: lsymbol) (m: mut_adt) : bool =
  List.exists (fun (d: data_decl) -> List.exists (fun c -> fst c = l) (snd d)) m *)

(*TODO: do we need this?*)


(*TODO: do we need vs?*)
(*let rec pat_constr_vars_inner (m: mut_adt) (vs: ty list) (p: pattern) : Svs.t =
  match p.pat_node with
| Pwild -> Svs.empty
| Pvar x -> if vsym_in_m m vs x then Svs.singleton x else Svs.empty
| Papp (f, ps) -> 
    (*only add variables in constructors of right type*)
    if constr_in_m f m then (*TODO: how to say tys = vs? For now, don't include - ruled out by uniformity of types
        although this is currently unsound I think (or maybe sound I just can't prove it)*)
        (*Also don't use length goals, implied by typing*)
      List.fold_right (fun x acc -> Svs.union (pat_constr_vars_inner m vs x) acc)
        (*A horrible way to write this: need to get patterns corresponding only to argument types in m*)
        (*But how to get m_params? Ugh - need better way to deal with this stuff*) 
      (*Also do not include params part - rely on uniform ADT restriction*)
        (List.map fst (List.filter (fun x -> vty_in_m' m (snd x)) (List.combine ps (f.ls_args)))) Svs.empty
  else Svs.empty
| Por (p1, p2) -> Svs.inter (pat_constr_vars_inner m vs p1) (pat_constr_vars_inner m vs p2)
| Pas (p', y) -> Svs.union (if vsym_in_m m vs y then Svs.singleton y else Svs.empty) (pat_constr_vars_inner m vs p')

(*Get strictly smaller (not just <=) vars. Recurse until we hit constructor*)
let rec pat_constr_vars (m: mut_adt) (vs: ty list) (p: pattern) : Svs.t =
match p.pat_node with
| Papp (_, _) -> pat_constr_vars_inner m vs p
| Por (p1, p2) -> Svs.inter (pat_constr_vars m vs p1) (pat_constr_vars m vs p2)
| Pas (p, y) -> pat_constr_vars m vs p
| _ -> Svs.empty*)

let upd_option (hd: vsymbol option) (x: vsymbol) : vsymbol option =
  match hd with
  | Some y -> if vs_equal x y then None else hd
  | None -> None

let upd_option_iter (x: vsymbol option) (xs: Svs.t) : vsymbol option =
  Svs.fold (fun v o -> upd_option o v) xs x

let check_var_case small hd v =
  hd = Some v || Svs.mem v small

let tm_var_case (small: Svs.t) (hd: vsymbol option) (t: term) : bool =
  match t.t_node with
| Tvar v -> check_var_case small hd v
| _ -> false

(*If jth element of tms is small variable, all [pat_constr_vars] in
  (nth j ps) should be added*)
let get_constr_smaller (small: Svs.t) (hd: vsymbol option) (m: mut_adt)
  (vs: ty list) (f: lsymbol) (tms: term list) (p: pattern) : Svs.t =
  match p.pat_node with
| Papp (f1, ps) -> if ls_equal f f1 then 
    List.fold_right Svs.union (List.map2 (fun t p -> if tm_var_case small hd t then pat_constr_vars m vs p else Svs.empty) tms ps) Svs.empty
else Svs.empty
| _ -> Svs.empty

let svs_remove_all (l: vsymbol list) (s: Svs.t) : Svs.t =
  List.fold_right Svs.remove l s

(*TODO: move/implement*)
let big_nth l n =
  if BigInt.lt n BigInt.zero then invalid_arg "big_nth" else
  let rec nth_aux l n =
    match l with
    | [] -> failwith "nth"
    | a::l -> if BigInt.is_zero n then a else nth_aux l (BigInt.pred n)
  in nth_aux l n

let rec check_decrease_fun (funs: (lsymbol * BigInt.t) list)
  (small: Svs.t) (hd: vsymbol option) (m: mut_adt) (vs: ty list) (t: term) : bool =
match t.t_node with
| Tapp(f, ts) ->
  begin match List.find_opt (fun y -> f = (fst y)) funs with
  | Some (_, i) ->
      (*Needs to be called on smaller variable at ith index*)
      begin match (big_nth ts i).t_node with
      | Tvar x -> Svs.contains small x && (*Check that map is uniform*)
      check_unif_map (ls_arg_inst f ts) &&
      List.for_all (check_decrease_fun funs small hd m vs) ts
      | _ -> false
      end
  | None -> (*not recursive*)
    List.for_all (check_decrease_fun funs small hd m vs) ts
  end
(*Other interesting case is Tcase*)
| Tcase (t, pats) -> 
  check_decrease_fun funs small hd m vs t &&
  (*TODO: merge these - maybe case inside function and just change the thing that is being union'ed*)
  List.for_all (fun tb ->
    let (p, t1) = t_open_branch tb in
    let toadd = begin match t.t_node with 
      | Tvar mvar -> if check_var_case small hd mvar then pat_constr_vars m vs p else Svs.empty
      | Tapp(c, tms) -> get_constr_smaller small hd m vs c tms p
      | _ -> Svs.empty
    end in
    let newsmall = Svs.union toadd (Svs.diff small p.pat_vars) in
    check_decrease_fun funs newsmall (upd_option_iter hd p.pat_vars) m vs t1
    ) pats

  (* begin match t.t_node with
  | Tvar mvar ->
    if hd = Some mvar || Svs.mem mvar small then
      List.for_all (fun tb ->
        let (p, t) = t_open_branch tb in
        (*Add smaller variables*)
        let newsmall = Svs.union (pat_constr_vars m vs p) (Svs.diff small (p.pat_vars)) in
        check_decrease_fun funs newsmall (upd_option_iter hd p.pat_vars) m vs t
        ) pats
      else 
        (*Non-smaller cases*)
        List.for_all (fun tb ->
          let (p, t) = t_open_branch tb in
          let newsmall = Svs.diff small (p.pat_vars) in
          check_decrease_fun funs newsmall (upd_option_iter hd p.pat_vars) m vs t
          ) pats
  | Tapp(c, tms) ->
    List.for_all (fun tb ->
      let (p, t) = t_open_branch tb in
      let newsmall = Svs.union (get_constr_smaller small hd m vs c tms p) (Svs.diff small (p.pat_vars)) in
      check_decrease_fun funs newsmall (upd_option_iter hd p.pat_vars) m vs t
      ) pats

  | _ -> List.for_all (fun tb ->
    let (p, t) = t_open_branch tb in
    let newsmall = Svs.diff small (p.pat_vars) in
    check_decrease_fun funs newsmall (upd_option_iter hd p.pat_vars) m vs t
    ) pats
  end *)
  (*START*)
  (*1*)
| Tlet(t1, tb) -> check_decrease_fun funs small hd m vs t1 &&
  let (x, t2) = t_open_bound tb in
  (*TODO: is this remove useless because x is guaranteed to be fresh?*)
  check_decrease_fun funs (Svs.remove x small) (upd_option hd x) m vs t2
| Tif(t1, t2, t3) -> check_decrease_fun funs small hd m vs t1 &&
  check_decrease_fun funs small hd m vs t2 &&
  check_decrease_fun funs small hd m vs t3
| Teps(tb) ->  let (x, t2) = t_open_bound tb in
  (*same as Tlet*) (*I think we can get rid of all of these*)
  check_decrease_fun funs (Svs.remove x small) (upd_option hd x) m vs t2
| Tquant(q, tq) -> let (vars, _, f) = t_open_quant tq in
  check_decrease_fun funs (svs_remove_all vars small) (upd_option_iter hd (Svs.of_list vars)) m vs f
| Tbinop(_, t1, t2) -> check_decrease_fun funs small hd m vs t1 && check_decrease_fun funs small hd m vs t2
| Tnot(t) -> check_decrease_fun funs small hd m vs t
| Tvar _ -> true
| Tconst _ -> true
| Ttrue -> true
| Tfalse -> true

let find_idx_list (l: (lsymbol * (vsymbol list * term)) list) m vs (candidates : BigInt.t list list) : BigInt.t list option =
  List.find_opt (fun il -> 
    List.for_all (fun ((f, (vars, t)), i) ->
      check_decrease_fun (List.combine (List.map fst l) il) Svs.empty (Some (big_nth vars i)) m vs t
      ) (List.combine l il)) candidates

(*START*)

(*TODO:*)
let mut_in_ctx (m: mut_adt) (kn: decl Mid.t) : bool =
  List.mem m (fst (get_ctx_tys kn))

let find_elt (f: 'a -> 'b option) (l: 'a list) : ('a * 'b) option =
  List.fold_right (fun x acc -> match f x with | None -> acc | Some y -> Some (x, y)) l None

 (*TODO: do we need mutual ADT?*)
let check_termination_aux kn (funs: (vsymbol list * term) Mls.t) :
      (BigInt.t Mls.t) option =
  if Mls.is_empty funs then None
  else 
    let l = Mls.bindings funs in
    let idxs = (get_idx_lists kn funs) in
    Option.bind
  (*TODO: skipping params for now - do we need?*)

  (find_elt (fun ((m, vs), cands) -> 
    (*Skip params, implied by typing*)
    if mut_in_ctx m kn then 
      find_idx_list l m vs (get_possible_index_lists cands)
  else None
    )
  idxs)
  (fun (_, idxs) -> 
    (*Match index with corresponding symbol*)
    Some (List.fold_right (fun x acc -> Mls.add (fst x) (snd x) acc) (List.combine (List.map fst l) idxs) Mls.empty)
    )

(*Other case: non-recursive*)
(*TODO: better way to check?*)
(*See if lsymbol appears in term*)
let rec ls_in_tm (l: lsymbol) (t: term) : bool =
  match t.t_node with
| Tapp (f, ts) -> ls_equal f l || List.exists (ls_in_tm l) ts
| Tif (t1, t2, t3) -> ls_in_tm l t1 || ls_in_tm l t2 || ls_in_tm l t3
| Tlet (t1, tb) -> ls_in_tm l t1 || let (_, t2) = t_open_bound tb in
  ls_in_tm l t2
| Tcase (t1, pats) -> ls_in_tm l t1 || List.exists (fun tb ->
    let (_, t) = t_open_branch tb in ls_in_tm l t) pats
| Teps tb -> let (_, t2) = t_open_bound tb in ls_in_tm l t2
| Tquant (_, tq) -> let (_, _ ,t2) = t_open_quant tq in ls_in_tm l t2
| Tbinop (_, t1, t2) -> ls_in_tm l t1 || ls_in_tm l t2
| Tnot f -> ls_in_tm l f
|_ -> false


let check_termination_strict kn d : decl =
  match d.d_node with
  | Dlogic ((l :: ls) as ld) ->

    let add acc (ls,ld) = Mls.add ls (open_ls_defn ld) acc in
    let syms = List.fold_left add Mls.empty ld in
    (*First, see if non-recursive*)
    let binds = Mls.bindings syms in
    if List.for_all (fun t -> List.for_all (fun l -> not (ls_in_tm l t)) (List.map fst binds)) (List.map (fun x -> snd (snd x)) binds) 
      then d else
    begin match (check_termination_aux kn syms) with
    | Some idxs -> (*TODO: do we actually need index info?*)
      (*TODO: change from int list to int maybe?*)
      let ldl =  List.map (fun (ls,((_,f),_)) -> (ls,((ls,f),[BigInt.to_int (Mls.find ls idxs)]))) ld in (*JOSH TODO delete to_int*)
      (*TODO: do we need to hashcons?*)
      { d_node = Dlogic ldl;
        d_news = d.d_news;
        d_tag  = d.d_tag;}
    | None -> raise (NoTerminationProof (fst l))
    end

  | _ -> d

let known_add_decl kn d =
  let kn = known_add_decl kn d in
  check_positivity kn d;
  check_foundness kn d;
  check_match kn d;
  let d = check_termination_strict kn d in
  (d, kn)

(** Records *)

exception EmptyRecord

let parse_record kn fll =
  let fs = match fll with
    | [] -> raise EmptyRecord
    | (fs,_)::_ -> fs in
  let ts = match fs.ls_args with
    | [{ ty_node = Tyapp (ts,_) }] -> ts
    | _ -> raise (BadRecordField fs) in
  let cs, pjl = match find_constructors kn ts with
    | [cs,pjl] -> cs, List.map (Opt.get_exn (BadRecordUnnamed (fs, ts))) pjl
    | _hd1 :: _hd2 :: _ -> raise (BadRecordCons (fs, ts))
    | _ -> raise (BadRecordType (fs, ts)) in
  let pjs = Sls.of_list pjl in
  let flm = List.fold_left (fun m (pj,v) ->
    if not (Sls.mem pj pjs) then raise (BadRecordField pj) else
    Mls.add_new (DuplicateRecordField pj) pj v m) Mls.empty fll in
  cs,pjl,flm

let make_record kn fll ty =
  let cs,pjl,flm = parse_record kn fll in
  let get_arg pj = Mls.find_exn (RecordFieldMissing pj) pj flm in
  fs_app cs (List.map get_arg pjl) ty

let make_record_update kn t fll ty =
  let cs,pjl,flm = parse_record kn fll in
  let get_arg pj = match Mls.find_opt pj flm with
    | Some v -> v
    | None -> t_app_infer pj [t] in
  fs_app cs (List.map get_arg pjl) ty

let make_record_pattern kn fll ty =
  let cs,pjl,flm = parse_record kn fll in
  let s = ty_match Mtv.empty (Option.get cs.ls_value) ty in
  let get_arg pj = match Mls.find_opt pj flm with
    | Some v -> v
    | None -> pat_wild (ty_inst s (Option.get pj.ls_value))
  in
  pat_app cs (List.map get_arg pjl) ty
