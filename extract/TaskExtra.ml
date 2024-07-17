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

open Ident
open Ty
open Term
open Decl
(* open Theory *)

(** Clone and meta history *)

(*Trying to switch see*)
(* module Stdecl = Theory.Stdecl1 *)

let stdecl_id (s: Stdecl1.t) : BigInt.t =
  Stdecl1.fold (fun t acc -> Hashcons.combine_big t.td_tag acc) s (BigInt.of_int 3)

(* module Stdecl = Hcpt.MakeSet(struct
  type t = tdecl
  let id td = BigInt.to_int td.td_tag 
end) *)
(* module HStdecl = Stdecl *)

(* type tdecl_set = Stdecl.t *)

module Wtds = Weakhtbl.Make(struct
  type t = tdecl_set
  let tag s = Weakhtbl.create_tag (stdecl_id s) (*(Stdecl.id s)*)
  let equal = (==) (*JOSH TODO equal*)
end)


let mk_tds s =
  Theory.Stdecl.fold Stdecl2.add s Stdecl2.empty

let tds_empty = Stdecl2.empty
let tds_singleton td = Stdecl2.singleton td

let tds_add = Stdecl2.add

let tds_equal = Stdecl2.equal
(* let tds_hash = Stdecl.hash 
JOSH SEE *)
let tds_compare = Stdecl2.compare

(* type clone_map = tdecl_set Mid.t
type meta_map = tdecl_set Mmeta.t *)

let cm_find cm th = Mid.find_def tds_empty th.th_name cm
let mm_find mm t = Mmeta.find_def tds_empty t mm

let cm_add cm th td = Mid.change (function
  | None -> Some (tds_singleton td)
  | Some tds -> Some (tds_add td tds)) th.th_name cm

let mm_add mm t td = Mmeta.change (function
  | None -> Some (tds_singleton td)
  | Some tds -> Some (tds_add td tds)) t mm

let mm_add mm t td = if t.meta_excl
  then Mmeta.add t (tds_singleton td) mm
  else mm_add mm t td

(** Task *)

(* type task = task_hd option

and task_hd = {
  task_decl  : tdecl;        (* last declaration *)
  task_prev  : task;         (* context *)
  task_known : known_map;    (* known identifiers *)
  task_clone : clone_map;    (* use/clone history *)
  task_meta  : meta_map;     (* meta properties *)
  task_tag   : Weakhtbl.tag; (* unique magical tag *)
} *)

(* let task_hd_equal t1 t2 = match t1.task_decl.td_node, t2.task_decl.td_node with
  | Decl {d_node = Dprop (Pgoal,p1,g1)}, Decl {d_node = Dprop (Pgoal,p2,g2)} ->
      Option.equal (==) t1.task_prev t2.task_prev &&
      pr_equal p1 p2 && t_equal_strict g1 g2
  | _ -> t1 == t2

let task_hd_hash t = Weakhtbl.tag_hash t.task_tag

let task_equal t1 t2 = Option.equal task_hd_equal t1 t2

let task_hash t = Option.fold ~some:(fun t -> BigInt.succ (task_hd_hash t)) ~none:BigInt.zero t *)

(* module Hstask = Hashcons.Make (struct
  type t = task_hd

  let equal t1 t2 = td_equal t1.task_decl t2.task_decl &&
                  task_equal t1.task_prev t2.task_prev

  let hash t =  (Hashcons.combine_big (td_hash t.task_decl) (task_hash t.task_prev))

  let tag i task = { task with task_tag = Weakhtbl.create_tag i }
end)

let mk_task decl prev known clone meta = Some (Hstask.hashcons {
  task_decl  = decl;
  task_prev  = prev;
  task_known = known;
  task_clone = clone;
  task_meta  = meta;
  task_tag   = Weakhtbl.dummy_tag;
}) *)

(* let task_known o = Option.fold ~some:(fun t -> t.task_known) ~none:Mid.empty   o
let task_clone o = Option.fold ~some:(fun t -> t.task_clone) ~none:Mid.empty   o
let task_meta  o = Option.fold ~some:(fun t -> t.task_meta)  ~none:Mmeta.empty o *)

let find_clone_tds task (th : theory) = cm_find (task_clone1 task) th
let find_meta_tds task (t : meta) = mm_find (task_meta1 task) t

(* constructors with checks *)

(* exception LemmaFound
exception GoalFound
exception GoalNotFound *)

(* let find_goal = function
  | Some {task_decl = {td_node = Decl {d_node = Dprop (Pgoal,p,f)}}} ->
      Some(p,f)
  | _ -> None

let task_goal task = match find_goal task with
  | Some (pr,_) -> pr
  | None        -> raise GoalNotFound

let task_goal_fmla task  = match find_goal task with
  | Some (_,f)  -> f
  | None        -> raise GoalNotFound

let task_separate_goal = function
  | Some {task_decl = {td_node = Decl {d_node = Dprop (Pgoal,_,_)}} as goal;
          task_prev = task} ->
      goal,task
  | _ -> raise GoalNotFound

let check_task task = match find_goal task with
  | Some _  -> raise GoalFound
  | None    -> task

let check_decl = function
  | {d_node = Dprop (Plemma,_,_)} -> raise LemmaFound
  | d -> d

let new_decl task d td =
  let (d1, kn) = known_add_decl (task_known task) (check_decl d) in
  let td1 = create_decl d1 in
  mk_task td1 (check_task task) kn (task_clone task) (task_meta task)

let new_decl task d td = try new_decl task d td with KnownIdent _ -> task *)

let new_clone task th td =
  let cl = cm_add (task_clone1 task) th td in
  mk_task td (check_task task) (task_known1 task) cl (task_meta1 task)

let new_meta task t td =
  let mt = mm_add (task_meta1 task) t td in
  mk_task td (check_task task) (task_known1 task) (task_clone1 task) mt

(* declaration constructors + add_decl *)

let add_decl task d = new_decl task d (create_decl d)

let add_ty_decl tk ts = add_decl tk (create_ty_decl ts)
let add_data_decl tk dl = add_decl tk (create_data_decl dl)
let add_param_decl tk ls = add_decl tk (create_param_decl ls)
let add_logic_decl tk dl = add_decl tk (create_logic_decl dl)
let add_ind_decl tk s dl = add_decl tk (create_ind_decl s dl)
let add_prop_decl tk k p f = add_decl tk (create_prop_decl k p f)

(* task constructors *)

let add_tdecl task td = match td.td_node with
  | Decl d -> new_decl task d td
  | Use th ->
      if Stdecl2.mem td (find_clone_tds task th) then task else
      new_clone task th td
  | Clone (th,_) -> new_clone task th td
  | Meta (t,_) -> new_meta task t td

let rec flat_tdecl task td = match td.td_node with
  | Decl { d_node = Dprop (Plemma,pr,f) } -> add_prop_decl task Paxiom pr f
  | Decl { d_node = Dprop (Pgoal,_,_) } -> task
  | Decl d -> new_decl task d td
  | Use th -> use_export task th td
  | Clone (th,_) -> new_clone task th td
  | Meta (t,_) -> new_meta task t td

and use_export task th td =
  if Stdecl2.mem td (find_clone_tds task th) then task else
  let task = List.fold_left flat_tdecl task th.th_decls in
  new_clone task th td

let use_export task th = use_export task th (create_use th)

let clone_export = clone_theory flat_tdecl

let add_meta task t al = new_meta task t (create_meta t al)

(* split theory *)

let theory_goals th names =
  if Opt.fold (fun _ s -> Spr.is_empty s) false names then Spr.empty else
  let named pr = match names with Some gs -> Spr.mem pr gs | _ -> true in
  let collect prs td = match td.td_node with
    | Clone (th, sm) -> (* do not reprove instantiations of lemmas *)
        Mpr.fold (fun o n prs -> match find_prop_decl th.th_known o with
          | (Plemma|Pgoal),_ -> Spr.remove n prs | _ -> prs) sm.sm_pr prs
    | Decl { d_node = Dprop ((Plemma|Pgoal),pr,_) } when named pr ->
        Spr.add pr prs
    | _ -> prs in
  List.fold_left collect Spr.empty th.th_decls

let split_theory th names init =
  let prs = theory_goals th names in
  if Spr.is_empty prs then [] else
  let split (task, acc) td = flat_tdecl task td, match td.td_node with
    | Decl { d_node = Dprop ((Plemma|Pgoal),pr,f) } when Spr.mem pr prs ->
        add_prop_decl task Pgoal pr f :: acc
    | _ -> acc in
  List.rev (snd (List.fold_left split (init, []) th.th_decls))

(* Generic utilities *)

let rec task_fold fn acc = function
  | Some task -> task_fold fn (fn acc task.task_decl) task.task_prev
  | None      -> acc

let rec task_iter fn = function
  | Some task -> fn task.task_decl; task_iter fn task.task_prev
  | None      -> ()

let task_tdecls = task_fold (fun acc td -> td::acc) []

let task_decls  = task_fold (fun acc td ->
  match td.td_node with Decl d -> d::acc | _ -> acc) []

(* Realization utilities *)

let check_use td = match td.td_node with
  | Use _ -> true
  | Clone _ -> false
  | _ -> assert false

let used_theories (task : task) =
  let used s =
    let th = match (Stdecl2.choose s).td_node with
      | Use th
      | Clone (th, _) -> th
      | _ -> assert false
    in
    if Stdecl2.exists_ check_use s then Some th else None
  in
  Mid.map_filter used (task_clone1 task)

let used_symbols thmap =
  let dict th = Mid.map (fun () -> th) th.th_local in
  let join _ = Mid.union (fun _ -> assert false) in
  Mid.fold join (Mid.map dict thmap) Mid.empty

let local_decls task symbmap =
  let rec skip t = function
    | { td_node = Use th } :: rest
      when id_equal t.th_name th.th_name -> rest
    | _ :: rest -> skip t rest
    | [] -> []
  in
  let rec filter acc = function
    | { td_node = Decl d } :: rest ->
        let id = Sid.choose d.d_news in
        (try filter acc (skip (Mid.find id symbmap) rest)
        with Not_found -> filter (d::acc) rest)
    | _ :: rest -> filter acc rest
    | [] -> List.rev acc
  in
  filter [] (task_tdecls task)

(* Selectors *)

exception NotTaggingMeta of meta
exception NotExclusiveMeta of meta

let on_meta t fn acc task =
  let add td acc = match td.td_node with
    | Meta (_,ma) -> fn acc ma
    | _ -> assert false
  in
  let tds = find_meta_tds task t in
  Stdecl2.fold add tds acc

let on_cloned_theory th fn acc task =
  let add td acc = match td.td_node with
    | Clone (_,sm) -> fn acc sm
    | Use _ -> acc
    | _ -> assert false
  in
  let tds = find_clone_tds task th in
  Stdecl2.fold add tds acc

let on_meta_excl t task =
  if not t.meta_excl then raise (NotExclusiveMeta t);
  let add td _ = match td.td_node with
    | Meta (_,ma) -> Some ma
    | _ -> assert false
  in
  let tds = find_meta_tds task t in
  Stdecl2.fold add tds None

let on_used_theory th task =
  let tds = find_clone_tds task th in
  Stdecl2.exists_ check_use tds

let on_tagged_ty t task =
  begin match t.meta_type with
    | MTty :: _ -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  let add td acc = match td.td_node with
    | Meta (_, MAty ty :: _) -> Sty.add ty acc
    | _ -> assert false
  in
  let tds = find_meta_tds task t in
  Stdecl2.fold add tds Sty.empty

let on_tagged_ts t task =
  begin match t.meta_type with
    | MTtysymbol :: _ -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  let add td acc = match td.td_node with
    | Meta (_, MAts ts :: _) -> Sts.add ts acc
    | _ -> assert false
  in
  let tds = find_meta_tds task t in
  Stdecl2.fold add tds Sts.empty

let on_tagged_ls t task =
  begin match t.meta_type with
    | MTlsymbol :: _ -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  let add td acc = match td.td_node with
    | Meta (_, MAls ls :: _) -> Sls.add ls acc
    | _ -> assert false
  in
  let tds = find_meta_tds task t in
  Stdecl2.fold add tds Sls.empty

let on_tagged_pr t task =
  begin match t.meta_type with
    | MTprsymbol :: _ -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  let add td acc = match td.td_node with
    | Meta (_, MApr pr :: _) -> Spr.add pr acc
    | _ -> assert false
  in
  let tds = find_meta_tds task t in
  Stdecl2.fold add tds Spr.empty


(* Exception reporting *)

let () = Exn_printer.register (fun fmt exn -> match exn with
  | LemmaFound ->   Format.pp_print_string fmt "Task cannot contain a lemma"
  | GoalFound ->    Format.pp_print_string fmt "The task already ends with a goal"
  | GoalNotFound -> Format.pp_print_string fmt "The task does not end with a goal"
  | NotTaggingMeta m ->
      Format.fprintf fmt "Metaproperty '%s' is not a symbol tag" m.meta_name
  | NotExclusiveMeta m ->
      Format.fprintf fmt "Metaproperty '%s' is not exclusive" m.meta_name
  | _ -> raise exn)

(* task1 : prefix
   lt : to reduce
   lk : suffix (reverse order)
   i : length of lt
*)
