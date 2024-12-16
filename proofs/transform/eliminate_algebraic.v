Require Import AssocList.
Require Import Task TermMap.
Require Import GenElts.
Require Import compile_match.


(*Here, we ignore metas since they don't exist in the core language.
  We also (mostly) ignore tuples, we can prove soundness separately
  because this is trivial - ex: tp_map just determines if we should compile or not.
  This just includes the critical path - when the ADT is actually axiomatized
  NOTE: we do not use keep_e, keep_r, and keep_m, kept_m - we will just have a generic
  selector function to determine which types to axiomatize and which to keep
  (esesntially, enc_ty/kept_no_case is a parameter).
  In contrast, we do need no_ind, no_inv, and no_sel (though these will also be abstract)
  because we need to prove soundness in all cases
  *)

From RecordUpdate Require Import RecordSet.
Record state := mk_state {
  mt_map : amap typesym funsym;       (* from type symbols to selector functions *)
  cc_map : amap funsym funsym;       (* from old constructors to new constructors *)
  cp_map : amap funsym (list funsym);  (* from old constructors to new projections *)
  (*pp_map : amap funsym funsym;       (* from old projections to new projections *)*)
  (*kept_m : amap typesym (list vty); *)        (* should we keep constructors/projections/Tcase for this type? *)
  (* tp_map : Mid.t (decl*theory_c); skipped tuple symbols *)
  (* inf_ts : Sts.t;               infinite types *)
  (* ma_map : Mts.t (list bool );     material type arguments *)
  (* keep_e : bool;                keep monomorphic enumeration types *)
  (* keep_r : bool;                keep non-recursive records *)
  (* keep_m : bool;                keep monomorphic data types *)
  no_ind : bool;                (* do not generate indexing functions *)
  no_inv : bool;                (* do not generate inversion axioms *)
  no_sel : bool;                (* do not generate selector *)
}.

(*Here, we can use coq-record-update*)

#[export] Instance etaX : Settable _ := settable! mk_state <mt_map; cc_map; cp_map; (*pp_map;*) no_ind; no_inv; no_sel>.
Import RecordSetNotations. 

(*Infer args for functions - hard to get it right*)

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
    match amap_get typevar_eq_dec s n1 with
    | Some ty3 => if vty_eqb t2 ty3 then Some s else None
    | None => Some (amap_set typevar_eq_dec s n1 t2)
    end
  | _, _ => if vty_eqb t1 t2 then Some s else None
  end.

(*Now use this to infer type map for functions*)
(*Is there a type substitution sigma such that sigma (args) = *)
Definition find_fpsym_map (f: fpsym) (tys: list vty) : option (amap typevar vty) :=
  fold_right2_opt ty_match amap_empty (s_args f) tys.

Definition find_param_vals (params: list typevar) (s: amap typevar vty) : list vty :=
  map (fun p => 
    match amap_get typevar_eq_dec s p with
    | Some t => t
    | None => vty_int (*not used so instantiate to anything*)
    end) params.

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
  end.

(*TODO: prove doesnt happen (how?)*)
Definition tfun_infer' (f: funsym) (tys: list vty) (tms: list term) : term :=
match tfun_infer f tys tms with | Some t => t | _ => tm_d end.
Definition tfun_infer_ret' (f: funsym) (tys: list vty) (tms: list term) : term * vty :=
match tfun_infer_ret f tys tms with | Some t => t | _ => (tm_d, vty_int) end.


Section ElimADT.

Variable keep_tys : typesym -> bool.

Definition enc_ty (t: vty) : bool :=
  match t with
  | vty_cons ts _ => negb (keep_tys ts)
  | _ => false
  end.

Section Rew.
Variable (gamma: context).
Variable (s: state).

(*TODO: bad, can we find the type differently?*)
Definition pat_match_ty (pats: list (pattern * term)) : option vty :=
  match pats with
  | nil => None
  | (p, t) :: _ => Typechecker.typecheck_term gamma t
  end.


(*Assume we have a list of banned variables (instantiate with term vars)*)
Variable badvars : list vsymbol.

(*It is often difficult to figure out what the type arguments for functions should be.
  We will do it as they do, trying to instantiate a type mapping*)


Fixpoint rewriteT (t: term) : term :=
  match t with
  | Tmatch t1 ty pats => 
    if enc_ty ty then
      let t1 := rewriteT t1 in
      let mk_br (x: option term * amap funsym term) (br: pattern * term) :=
        let w := fst x in
        let m := snd x in
        let e := rewriteT (snd br) in
        match (fst br) with
        | Pconstr cs tys pl =>
          let add_var e p pj :=
            match p with
            | Pvar v => Tlet (Tfun pj [snd v] [t1]) v e
            | _ => tm_d (*NOTE: default, because we never hit it anyway by assumption*)
            end
            in
            let pjl := amap_get_def funsym_eq_dec s.(cp_map) cs nil in 
             (*match amap_get funsym_eq_dec s.(cp_map) cs with
            | Some cp => cp
            | None => nil (*TODO: prove don't hit (basically, will prove by knowing that all
              defined types appeared before and hence have already been added to map)*)
            end in*)
            let e := fold_left2' add_var pl pjl e in
            (w, amap_set funsym_eq_dec m cs e)
        | Pwild => (Some e, m)
        | _ => (*Prove don't hit*) x
        end
      in
      let res := fold_left mk_br pats (None, amap_empty) in
      let w := fst res in
      let m := snd res in (*gives map constructors to new terms*)
      let find x := 
        match amap_get funsym_eq_dec m x with
        | Some e => e
        | None => match w with | Some x => x | None => (*impossible*) tm_d end
        end
      in
      let ts := match ty with | vty_cons ts _ => ts | _ => ts_d (*impossible*) end in
      match map find (get_constructors gamma ts) with
      | [t] => t
      | tl => (*Get *) 
        (*Get the type - NOTE: use fact that not empty*)
        let ty1 := match pat_match_ty pats with | Some t => t | None => ty end in 
        tfun_infer' (amap_get_def typesym_eq_dec s.(mt_map) ts id_fs) (ty :: repeat ty1 (length tl))
          (t1 :: tl) (*TODO: prove not default*)
        (*return type: list a -> b -> b -> b, so give [vty_var a; ty1] if a is list var
          (types of args are [(ty :: repeat ty1 (length tl))])*)
          (*Don;t know if this type is right?*)
        (*this gives projection*) (*(map vty_var (ts_args ts) ++ [ty1]) (t1 :: tl) (*what is ty?*)*) 
        (*Type should be original type of term - can we tell this?
          arguments have type: [ty; ty1; ty1, ... ty1] if elements in pat match have type ty1. 
          We may need to carry around this information*)
      end
    else t_map rewriteT (rewriteF nil true) t
  | Tfun ls tys args => (*map old constrs to new constr*)
    if ls.(f_is_constr) && enc_ty (f_ret ls) (*we can just pass in return type because only depends on typesym*)
    then Tfun (amap_get_def funsym_eq_dec s.(cc_map) ls id_fs) tys args
    else t_map rewriteT (rewriteF nil true) t
  (*Don't have projections*)
  | _ => t_map rewriteT (rewriteF nil true) t
  end
with rewriteF (av: list vsymbol) (sign: bool) (f: formula) : formula := 
  match f with
  | Fmatch t1 ty1 pats =>
    if enc_ty ty1 then
      let t1 := rewriteT t1 in
      let av' := set_diff vsymbol_eq_dec av (tm_fv t1) in (*TODO: what is this doing?*)
      let mk_br (x: option formula * amap funsym (list vsymbol * formula)) br :=
        let p := fst br in
        let e := snd br in
        let w := fst x in
        let m := snd x in
        let e := rewriteF av' sign e in
        match p with
        | Pconstr cs tys pl =>
          let get_var p := match p with
            | Pvar v => v
            | _ => (*TODO: prove don't hit*) vs_d
          end in
          (w, amap_set funsym_eq_dec m cs (map get_var pl, e))
        | Pwild => (Some e, m)
        | _ => (*TODO: prove dont hit*) x
        end in
      let res := fold_left mk_br pats (None, amap_empty) in
      let w := fst res in
      let m := snd res in
      let find cs :=
        let res := match amap_get funsym_eq_dec m cs with
        | Some y => y
        | None => (*Need fresh vars - TODO: *)
            let projs := amap_get_def funsym_eq_dec (s.(cp_map)) cs nil in
            let names := gen_strs (length projs) badvars in
            (*NOTE: I think type should be ty_subst (s_params s) [ty1] (s_ret s) - they use t_app_infer*)
            let vars := map2 (fun n (p: funsym) => (n, ty_subst (s_params p) [ty1] (f_ret p))) names projs : list vsymbol in
            (vars, match w with | Some y => y | None => Ftrue end) (*TODO: prove dont hit*)
        end
        in
        let vl := fst res in let e := snd res in
        let hd := tfun_infer' (amap_get_def funsym_eq_dec (s.(cc_map)) cs id_fs) (map snd vl) (map Tvar vl) in
        match t1 with
        | Tvar v => if in_dec vsymbol_eq_dec v av then
          let hd := Flet hd v e in if sign then fforalls vl hd else fexists vl hd
          else
          let hd := Feq ty1 t1 hd (*TODO: ty1?*) in if sign then fforalls vl (Fbinop Timplies hd e)
          else fexists vl (Fbinop Tand hd e)
        | _ => let hd := Feq ty1 t1 hd (*TODO: ty1?*) in if sign then fforalls vl (Fbinop Timplies hd e)
          else fexists vl (Fbinop Tand hd e)
        end
      in
      let ts :=
        match ty1 with | vty_cons ts _ => ts | _ => ts_d end (*TODO: show dont hit*) in
      let op := if sign then (Fbinop Tand) else (Fbinop Tor) in
      match map_join_left find op (get_constructors gamma ts) with
      | Some f => f
      | None => Ftrue (*TODO: prove don't hit*)
      end
    else f_map_sign (fun _ => rewriteT) (rewriteF nil) sign f
  | Fquant q v f1 =>
    if (quant_eqb q Tforall && sign) || (quant_eqb q Texists && negb sign) then
      let av := fold_right (set_add vsymbol_eq_dec) [v] av in
      Fquant q v (rewriteF av sign f1)
    else f_map_sign (fun _ => rewriteT) (rewriteF nil) sign f
  | Fbinop o _ _ =>
    if (binop_eqb o Tand && sign) || (binop_eqb o Tor && negb sign) then
      f_map_sign (fun _ => rewriteT) (rewriteF av) sign f (*not nil*)
    else f_map_sign (fun _ => rewriteT) (rewriteF nil) sign f
  | Flet t1 _ _ =>
    let av := set_diff vsymbol_eq_dec av (tm_fv t1) in
    f_map_sign (fun _ => rewriteT) (rewriteF av) sign f 
  | _ => f_map_sign (fun _ => rewriteT) (rewriteF nil) sign f
  end.

End Rew.


(*Generate axioms*)

Definition add_param_decl (t: task) (f: funsym) : task :=
  (abs_fun f :: task_gamma t, task_delta t, task_goal t).

Definition add_axiom (t: task) (n: string) (f: formula) : task :=
  (task_gamma t, (n, f) :: task_delta t, task_goal t).

(*In all of these, we separate out the definition of the axioms/funsyms and the
  "stateful" (in the monadic sense) function that updates the task and state*)

(*The selector axiom for a given typesym and constructor list*)
(*NOTE: the cc_map is probably the identity map but we still keep it because
  it is not (for some reason) in the full version*)
(*TODO: need condition that all funsyms in csl appear in cc_map*)
Definition selector_axiom (cc_map : amap funsym funsym) 
  (ts: typesym) (ty: vty) (csl: list funsym) : funsym * list (string * formula) (*list (funsym * formula)?*) :=
  (* declare the selector function *)
  let mt_id : string := ("match_" ++ ts_name ts)%string in
  (*TODO: does it need to be fresh?*)
  let mt_ty : vty := vty_var "a"%string in
  (* let mt_ty = ty_var (create_tvsymbol (id_fresh "a")) in *)
  let mt_al := ty :: rev_map (fun _ => mt_ty) csl in
  let mt_ls := funsym_noconstr_noty mt_id mt_al mt_ty in
  (* let mt_map2 := amap_set typesym_eq_dec s.(mt_map) ts mt_ls in *)
  (* define the selector function *)
  (*Generate new vars*)
  let varnames := gen_names (length csl) "z"%string nil in
  let mt_vl : list vsymbol := rev_map (fun x => (x, mt_ty)) varnames in
  (* let mt_vs _ = create_vsymbol (id_fresh "z") mt_ty in *)
  (* let mt_vl = List.rev_map mt_vs csl in *)
  let mt_tl := rev_map Tvar mt_vl in
  let mt_add (cs: funsym) t :=
    let id := (mt_id ++ "_" ++ (s_name cs))%string in
    (* let id = mt_ls.ls_name.id_string ^ "_" ^ cs.ls_name.id_string in *) 
    (* let pr = create_prsymbol (id_derive id cs.ls_name) in *)
    (*Create new vars - they can be the same among axioms (TODO: inefficient)*)
    let varnames2 := gen_names (length (s_args cs)) "u"%string varnames in
    let vl := rev (combine varnames2 (s_args cs)) in
    (* let vl = List.rev_map (create_vsymbol (id_fresh "u")) cs.ls_args in *)
    let newcs := amap_get_def funsym_eq_dec cc_map cs id_fs in (*TODO: show have*)
    let hd := tfun_infer' newcs (rev_map snd vl) (rev_map Tvar vl) in (*TODO: is return type right? - they say f_ret cs*)
    let hd := tfun_infer' mt_ls ((f_ret cs) :: map snd mt_vl) (hd :: mt_tl) in
    let vl := rev_append mt_vl (rev vl) in
    let ax := fforalls vl (Feq mt_ty hd t) in
    (id, ax)
  in 
  (mt_ls, map2 mt_add csl mt_tl).

(*INVARINT: mt_map is fst (selector_axiom)*)

Definition add_task_axioms (t: task) (axs: list (string * formula)) : task :=
  fold_left (fun acc x => add_axiom acc (fst x) (snd x)) axs t.

(*NOTE: will prob need to separate out for proof purposes (e.g. map2 vs fold_left2 and separate function)*)
Definition add_selector_aux (st: state * task) (ts: typesym) (ty: vty) (csl: list funsym) :=
  let s := fst st in
  let tsk := snd st in
  if s.(no_sel) then (s, tsk) else
  let sel := selector_axiom s.(cc_map) ts ty csl in
  let mt_ls := fst sel in
  let axms := snd sel in
  let tsk := add_param_decl tsk mt_ls in
  let tsk := add_task_axioms tsk axms in
  (*update state*)
  let mt_map2 := amap_set typesym_eq_dec s.(mt_map) ts mt_ls in
  (s <|mt_map := mt_map2|>, tsk).

(*Don't need selector for types with single constructor because trivial.
  NOTE: does this cause any problems with eliminating singleton types (e.g. user defined tuple)
  need to see in rewriteT*)
Definition add_selector (acc : state * task) (ts: typesym) (ty: vty) (x: list funsym) :
  state * task :=
  match x with
  | [_] => acc
  | csl => add_selector_aux acc ts ty csl
  end.

Definition mapi {A B: Type} (f: nat -> A -> B) (l: list A) : list B :=
  map (fun x => f (fst x) (snd x)) (combine (seq 0 (length l)) l).

(*Again, define indexer axiom*)
Definition indexer_axiom (cc_map : amap funsym funsym)  
  (ts: typesym) (ty : vty) (csl : list funsym) : funsym * list (string * formula) :=
  (* declare the indexer function *)
  let mt_id := ("index_" ++ (ts_name ts))%string in
  let mt_ls := funsym_noconstr_noty mt_id [ty] vty_int in
  (* define the indexer function *)
  let mt_add idx (cs: funsym) :=
    let id := (mt_id ++ "_" ++ (s_name cs))%string in
    (* let pr = create_prsymbol (id_derive id cs.ls_name) in *)
    let varnames := gen_names (length (s_args cs)) "u" nil in
    let vl := rev (combine varnames (s_args cs)) in
    let newcs := amap_get_def funsym_eq_dec cc_map cs id_fs in
    (*NOTE: THESE TYPES MAY BE WRONG!*)
    let hd := tfun_infer' newcs (rev (map snd vl)) (rev_map Tvar vl) in
    (* let hd = fs_app newcs (List.rev_map t_var vl) (Option.get cs.ls_value) in *)
    let ax := Feq vty_int (tfun_infer' mt_ls (*TODO: what is hd type?*) [(f_ret newcs)] [hd] )  
      (Tconst (ConstInt (Z.of_nat idx))) in
    let ax := fforalls (rev vl) ax in
    (id, ax) in
  (mt_ls, mapi mt_add csl). 

Definition add_indexer_aux (st: state * task) (ts: typesym) (ty : vty) (csl : list funsym) : state * task :=
  let s := fst st in
  let tsk := snd st in
  let indexer := indexer_axiom s.(cc_map) ts ty csl in
  let mt_ls := fst indexer in
  let axms := snd indexer in
  (*update task*)
  let tsk := add_param_decl tsk mt_ls in
  let tsk := add_task_axioms tsk axms in
  (s, tsk).

Definition t_neq (ty: vty) (t1 t2: term) : formula :=
  Fnot (Feq ty t1 t2).

(*Discriminator axioms - there should be O(n^2) - 1 per pair of constructors*)

(*Generic: apply function of type A -> A -> B to each pair (a_i, a_j) of elements in l,
  where i < j*)
Fixpoint map_pairs {A B: Type} (f: A -> A -> B) (l: list A) : list B :=
  match l with
  | x :: xs => map (f x) xs ++ map_pairs f xs
  | nil => nil
  end.

(*Here, only axioms - TODO: do we want to index by funsyms: ie, return (funsym * funsym * formula)*)
Definition discriminator_axioms (cc_map : amap funsym funsym) (ts: typesym) (ty: vty) (csl: list funsym) : 
  list (string * formula) :=
  let d_add (c1: funsym) (c2: funsym) : (string * formula) :=
    let i : string := ((s_name c1) ++ "_" ++ (s_name c2))%string in
    (* let pr = create_prsymbol (id_derive id ts.ts_name) in *)
    (*Create vars - TODO: does it have to be fresh against some vars?*)
    let ul := rev (combine (gen_names (length (s_args c1)) "u" nil) (s_args c1)) in
    let vl := rev (combine (gen_names (length (s_args c2)) "v" nil) (s_args c2)) in
    (* let ul := rev_map (create_vsymbol (id_fresh "u")) c1.ls_args in
    let vl = List.rev_map (create_vsymbol (id_fresh "v")) c2.ls_args in *)
    let newc1 := amap_get_def funsym_eq_dec (cc_map) c1 id_fs in
    let newc2 := amap_get_def funsym_eq_dec (cc_map) c2 id_fs in
    let t1 := tfun_infer' newc1 (rev (map snd ul)) (rev_map Tvar ul) in
    let t2 := tfun_infer' newc2 (rev (map snd vl)) (rev_map Tvar vl) in
    (* let t1 = fs_app newc1 (List.rev_map t_var ul) ty in
    let t2 = fs_app newc2 (List.rev_map t_var vl) ty in *)
    let ax := t_neq ty t1 t2 in
    let ax := fforalls (rev vl) ax in
    let ax := fforalls (rev ul) ax in
    (i, ax)
  in
  map_pairs d_add csl.


Definition add_discriminator (st: state * task) (ts: typesym) (ty: vty) (csl: list funsym) : state * task :=
  let s := fst st in
  let tsk := snd st in
  let axs := discriminator_axioms s.(cc_map) ts ty csl in
  (s, add_task_axioms tsk axs).

(*TODO: see if we want to do this still - are there types with more than 16 constructors?*)
Definition add_indexer (acc: state * task) (ts: typesym) (ty: vty) (cs: list funsym) := 
  match cs with
  | [_] => acc
  | csl => if negb (fst acc).(no_ind) then add_indexer_aux acc ts ty csl
    else if Nat.leb (length csl) 16 then add_discriminator acc ts ty csl 
    else acc
  end.

(*NOTE: complete_projections just copies over projections if they exist.
  We do not have any projections in our data, so we only implement the "None" case.
  TODO: we will need a predicate/typing rule asserting that projection is correct if it exists
  or something (not sure exactly what we need - will certainly need typing info) *)
(*ONLY creates function symbols - so projections are just user-named functions essentially - spec should
  just be that this produces SOME function symbol of the right type*)

(*A functional version of the projection function symbol*)
Definition projection_syms (c: funsym) : list funsym :=
  let conv_p (i: nat) (ty: vty) :=
    let id := ((s_name c) ++ "_proj_" ++ (nat_to_string i))%string in
    (*TODO: do we need option?*)(funsym_noconstr_noty id [f_ret c] ty)
  in
  mapi conv_p (s_args c).


Definition complete_projections (csl: list funsym) : list (funsym * list funsym) :=
  map (fun c => (c, projection_syms c)) csl.

(*Projection axioms*)
(*We do NOT thread cp_map, pp_map*)

(*What to do about [pp_map] - we do not have old projections.
  Also we never access pp_map outside of this function - useless to us *)
(*We consider projection axioms for a single constructor and list of projection symbols
  (given by [projection_names]) - pj_add from before*)
Definition projection_axioms (cc_map: amap funsym funsym) 
  (cs: funsym) (pl: list funsym) : list (funsym * (string * formula)) :=
  (* declare and define the projection functions *)
  (*Fresh vars TODO*)
  let vl := combine (gen_names (length (s_args cs)) "u" nil) (s_args cs) in
  (* let vl = List.map (create_vsymbol (id_fresh "u")) cs.ls_args in *)
  let tl := map Tvar vl in
  let hd := tfun_infer' (amap_get_def funsym_eq_dec (cc_map) cs id_fs)
    (map snd vl) tl in
  (* let hd = fs_app (Mls.find cs state.cc_map) tl (Option.get cs.ls_value) in *)
  (*TODO: added ty*)
  (*NOTE: not creating new funsym because we don't have unique IDs, just use pj*)
  let add (*(x: list funsym * amap funsym funsym * task)*) (tty: term * vty) (pj: funsym) :
      (funsym * (string * formula)) :=
      (* list funsym * amap funsym funsym * task := *)
    let t := fst tty in let ty := snd tty in
    (* let pj := option_get_Option.get pj in *)
    (*NOTE: since we don't have unique ids, is this just pj? Is that a problem?*)
    (* let ls := funsym_noconstr_noty (s_name pj) (s_args pj) (f_ret pj) in *)
    let ls := pj in
      (* match Mls.find pj pp_map with
      | pj -> pj,pp_map
      | exception Not_found ->
        let id = id_clone pj.ls_name in
        let ls = create_lsymbol id pj.ls_args pj.ls_value in
        ls,Mls.add pj ls pp_map
    in *)
    (* let tsk := add_param_decl tsk ls in *) (*TODO*)
    let id := ((s_name ls) ++ "'def")%string in
    (* let id = id_derive (ls.ls_name.id_string ^ "'def") ls.ls_name in
    let pr = create_prsymbol id in *)
    let hh := tfun_infer' ls [(f_ret cs)] [hd] in
    (* let hh = t_app ls [hd] t.t_ty in *)
    let ax := fforalls vl (Feq ty hh t) in
    (* let tsk := add_axiom tsk id ax in *) (*TODO*)
    (*Ignore metas*)
    (* let ax = t_forall_close vl [] (t_equ hh t) in
    let tsk = add_prop_decl tsk Paxiom pr ax in
    let tsk = add_meta_model_projection tsk ls in *)
    (ls, (id, ax))
  in
  map2 add (combine tl (map snd vl)) pl.


(*NOTE: this changed A LOT from the Why3 version, need to make sure it is correct (and possibly
  harder to prove equivalent)*)
Definition add_projections {A B: Type} (st: state * task) (_ts : A) (_ty : B) (csl: list funsym) :
  state * task :=
  let s := fst st in
  let tsk := snd st in
  (*For each constructor, get projections and axioms, add projection funsym and axioms to task*)
  let tsk := fold_left (fun acc c => 
    let projs := projection_axioms s.(cc_map) c (projection_syms c) in
    fold_left (fun tsk x => 
      let pj := fst x in
      let ax := snd x in
      add_axiom (add_param_decl tsk pj) (fst ax) (snd ax) 
    ) projs acc
    ) csl tsk in
  (*update state with projections - should be just rev (projection_syms) (TODO make sure)*)
  let cp_map2 := fold_left (fun acc x => amap_set funsym_eq_dec acc x (rev (projection_syms x))) csl s.(cp_map) in
  let st := s <| cp_map := cp_map2 |> in
  (st, tsk).

(*TODO: do we need state at all (other than maybe constructor map) - we know exactly what is
  in the state for each - really should just need task*)

Definition inversion_axiom (cc_map: amap funsym funsym) 
  (ts: typesym) (ty: vty) (csl: list funsym) : string * formula :=
  (* add the inversion axiom *)
  let ax_id := ((ts_name ts) ++ "_inversion")%string in
  (* let ax_pr = create_prsymbol (id_derive ax_id ts.ts_name) in *)
  (*TODO: fresh?*)
  let ax_vs := (gen_name "u"%string nil, ty) in 
  let ax_hd := Tvar ax_vs in
  let mk_cs (cs: funsym) : formula :=
    (*NOTE: we know the pjl from the projections*)
    let pjl := rev (projection_syms cs) in
    (* let pjl := amap_get_def funsym_eq_dec s.(cp_map) cs nil in  *)
    (*NOTE: change app to also give return type*)
    let app pj := tfun_infer_ret' pj [ty] [ax_hd] in
    (* let app pj = t_app_infer pj [ax_hd] in *)
    let cs := amap_get_def funsym_eq_dec cc_map cs id_fs in
    (* let cs = Mls.find cs state.cc_map in *)
    let pjl' := map app pjl in
    Feq ty ax_hd (tfun_infer' cs (map snd pjl') (map fst pjl'))
    (* t_equ ax_hd (fs_app cs (List.map app pjl) ty) in *)
  in
  let ax_f := map_join_left' Ftrue mk_cs (Fbinop Tor) csl in
  let ax_f := Fquant Tforall ax_vs ax_f (*t_forall_close [ax_vs] [] ax_f in*) in
  (ax_id, ax_f).


Definition add_inversion (st: state * task) (ts: typesym) (ty: vty) (csl: list funsym) :
  state * task :=
  let s := fst st in let tsk := snd st in
  if s.(no_inv) then st else
  let inv := inversion_axiom s.(cc_map) ts ty csl in
  (s, add_axiom tsk (fst inv) (snd inv)).

(*TODO: since we don't have builtin projections, we can't do the
  [kept_no_case] part for projections. We don't implement it at all.
  TODO: need to figure out: do we prove only a subset of allowed behaviors sound?
  or can we prove the rest at the higher level - assuming something about projections, etc
  Or should we add projections? Need to figure this out!*)

Definition add_axioms (st: state * task) (d: typesym * list funsym) : state * task :=
  let s := fst st in
  let tsk := snd st in
  let ts := fst d in
  let csl := snd d in
  (*NOTE: might be very easy to infer all types - might not need infer, might just all be typesym args*)
  let ty := vty_cons ts (map vty_var (ts_args ts)) in
  (*TODO: SKIP KEPT_NO_CASE*)
  (*Just add axioms for all maybe?*)
  if negb (null (ts_args ts)) (*|| negb (amap_mem typesym_eq_dec ts s.(kept_m))*) then
    (* declare constructors as abstract functions *)
    let cs_add (st: state * task) (cs: funsym) :=
      let s := fst st in let tsk := snd st in
      let id := s_name cs in (*TODO: no clone, is this ok*)
      let ls := funsym_noconstr_noty id (s_args cs) (f_ret cs) in (*TODO: this is ls*)
      (* let ls = create_lsymbol id cs.ls_args cs.ls_value in *)
      (s <| cc_map := amap_set funsym_eq_dec s.(cc_map) cs ls |>, add_param_decl tsk ls)
      (* { state with cc_map = Mls.add cs ls state.cc_map },add_param_decl task ls *)
    in
    let st := fold_left cs_add csl st in
    (* add selector, projections, and inversion axiom *)
    let st := add_selector st ts ty csl in
    let st := add_indexer st ts ty csl in
    let st := add_projections st ts ty csl in
    add_inversion st ts ty csl
  else st.

(*Skip [add_tags] and finding infinite types - only deals with metas*)

(*let's go opposite direction for now*)
(*NOTE: basically their task is a (for our purposes) : list decl,
  where decl is either def or prop (axiom/lemma/goal). We should have way to transform
  their task into ours/vice versa - we want unified function for this
  Didn't encounter before because e.g. elim_inductive and definition only work on defs,
  not on hpotheses or goal. Structure of tasks should be:
  1. there is a single goal to be proved (at end/beginning of list)
  2. this goal arose from goal or lemma decl originally
  3. any prior goals are ignored, any prior lemmas are effectively axioms *)

(*Ignore tuples, so don't need 2nd comp function. Instead we split into
  2 functions: 1 for defs, 1 for hyps/goal*)

Definition add_ty_decl (t: task) (ts: typesym) : task :=
  (abs_type ts :: task_gamma t, task_delta t, task_goal t).
 
(*Add subset of mut args*)
(*TODO: do we need to do this? I suppose we could just say that all tuples should be kept with this?*)
(*We will need to prove inhab, etc *)
(* Definition add_data_decl (t: task) (m: mut_adt) (l: list alg_datatype) :=
  (datatype_def (mk_mut l (m_params m) (m_nodup m))) *)

(*TODO: do we need all of [def_map]? Can we assume inductives and recursive functions gone
  already?*)


(*Instantiate badvars with term variables*)
Definition rewriteT' gamma s t :=
  rewriteT gamma s ((tm_fv t) ++ (tm_bnd t)) t.
Definition rewriteF' gamma s x y f :=
  rewriteF gamma s ((fmla_fv f) ++ (fmla_bnd f)) x y f.

Definition add_def (d: def) (t: task) : task :=
  (d :: task_gamma t, task_delta t, task_goal t).

(*Add mut with params from given mut and list of ADTs (should be subset)*)
Definition add_mut (m: mut_adt)(tys: list alg_datatype) (t: task) : task :=
  add_def (datatype_def (mk_mut tys (m_params m) (m_nodup m))) t.

Definition comp_ctx (d: def) (st: state * task) : state * task :=
  let s := fst st in let tsk := snd st in
  match d with
  | datatype_def m =>
    let dl := typs m in
    (*Ignore keeping any types (for now, need to figure out)*)
    (* let used := get_used_syms_decl d in *)
    (*Ignore all [kept_no_case] parts*)
    (* add type declarations *)
    (*Only add those not excluded*)
    (* let concrete (a: alg_datatype) : bool :=  amap_mem typesym_eq_dec (s.(kept_m)) (adt_name a) in *)
     (* Mts.mem (fst d) state.kept_m || kept_no_case used state d in *)
    let '(dl_concr, dl_abs) := partition (fun a => keep_tys (adt_name a)) dl in
    (*TODO: this does NOT preserve order, but keeps a well-typed permutation, see if this is problem*)
    let tsk := List.fold_left (fun t a => add_ty_decl t (adt_name a)) dl_abs tsk in
    let tsk := if null dl_concr then tsk else add_mut m dl_concr tsk in
    (* add needed functions and axioms *)
    let st := List.fold_left add_axioms (map (fun a => (adt_name a, adt_constr_list a)) dl) (s,tsk) in
    (* add the tags for infinite types and material arguments *)
    (* let mts := List.fold_right (fun '(t,l) => Mts.add t l) dl amap_empty in
    let st := List.fold_left (add_tags mts) st dl in *)
    (* return the updated state and task *)
    st
  | _ => 
    (*rewriting case*)
    (*TODO: should it be task_gamma tsk instead of separate gamma? prob*)
    (s, add_def (TaskGen.def_map (rewriteT' (task_gamma tsk) s) (rewriteF' (task_gamma tsk) s nil true) d) tsk)
  end.

(*And for formula (easy)*)
(* Definition comp_fmla (f: formula) (st: state * task) : state * task :=
let s := fst st in let tsk := snd st in
  (s, add_def (TaskGen.def_map (rewriteT' (task_gamma tsk) s) (rewriteF' (task_gamma tsk) s nil true) d) tsk). *)

(*Fold version - dont use Trans.fold, easier to manually thread state through*)
Definition fold_comp (st: state) : trans :=
  fun t => 
    let x := fold_left (fun x y => comp_ctx y x) (task_gamma t) (st, t) in
    let st1 := fst x in
    let tsk1 := snd x in
    let del1 := map (rewriteF' (task_gamma tsk1) st1 nil true) (map snd (task_delta tsk1)) in
    let g1 := rewriteF' (task_gamma tsk1) st1 nil true (task_goal tsk1) in
    [(task_gamma tsk1, (combine (map fst (task_delta tsk1)) del1), g1)]. 

(*No infinte types or anything so just give state*)

Section FullTrans.
(*Parameterize by no_ind, no_inv, no_sel*)
Variable (noind: bool) (noinv: bool) (nosel: bool).

(*I suppose we could make all params, but prob not*)
Definition empty_state : state := {| mt_map := amap_empty; cc_map := amap_empty;
  cp_map := amap_empty; (*pp_map := amap_empty;*) no_ind := noind; no_inv := noinv; no_sel := nosel|}.


Definition eliminate_match : trans :=
  compose_trans compile_match (fold_comp empty_state).

(*Note that compile_match is the same - with extra meta stuff we don't care about*)

Definition eliminate_algebraic : trans :=
  compose_trans compile_match (fold_comp empty_state).

End FullTrans.

End ElimADT.

