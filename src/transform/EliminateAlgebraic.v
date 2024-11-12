(* Require Import TermFuncs PatternComp.
(** Compile match patterns *)
Check t_open_branch.
Fixpoint rewriteT (t: term_c) :=
  match (t_node_of t) with
  | Tcase t bl =>
    let t1 := rewriteT t in
    let rest := compile_bare t_case_close t_let_close_simp [t1] 
      (map (fun b => 
        )) 


let rec rewriteT t0 = match t0.t_node with
  | Tcase (t,bl) ->
      let t = rewriteT t in
      let mk_b b = let p,t = t_open_branch b in [p], rewriteT t in
      let mk_case = t_case_close and mk_let = t_let_close_simp in
      let res = Pattern.compile_bare ~mk_case ~mk_let [t] (List.map mk_b bl) in
      t_attr_copy t0 res
  | _ -> t_map rewriteT t0

let compile_match = Trans.decl (fun d -> [decl_map rewriteT d]) None *)