Require Import AssocList.
Require Import Task TermMap.
Require Import GenElts.
Require Import compile_match.
Set Bullet Behavior "Strict Subproofs".


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

(* From RecordUpdate Require Import RecordSet. *)
(*Record state := mk_state {
  mt_map : amap typesym funsym;       (* from type symbols to selector functions *)
  (*cc_map : amap funsym funsym;*)       (* from old constructors to new constructors - NOTE: just
    make this a parameter*)
  cp_map : amap funsym (list funsym);  (* from old constructors to new projections *)
  (*pp_map : amap funsym funsym;       (* from old projections to new projections *)*)
  (*kept_m : amap typesym (list vty); *)        (* should we keep constructors/projections/Tcase for this type? *)
  (* tp_map : Mid.t (decl*theory_c); skipped tuple symbols *)
  (* inf_ts : Sts.t;               infinite types *)
  (* ma_map : Mts.t (list bool );     material type arguments *)
  (* keep_e : bool;                keep monomorphic enumeration types *)
  (* keep_r : bool;                keep non-recursive records *)
  (* keep_m : bool;                keep monomorphic data types *)
  (*NOTE: parameterize by these because we don't change anything - could do by typesym*)
  (* no_ind : bool;                (* do not generate indexing functions *)
  no_inv : bool;                (* do not generate inversion axioms *)
  no_sel : bool;                do not generate selector *)
}.*)

(*Here, we can use coq-record-update*)

(* #[export] Instance etaX : Settable _ := settable! mk_state <mt_map; (*cc_map;*) cp_map (*pp_map;*) (*no_ind; no_inv; no_sel*)>.
Import RecordSetNotations.  *)

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

(*NOTE: originally, had generic keep_tys: typesym -> bool.
  The problem is if we choose to keep some ADTs in a mutual block but not others,
  things become very complicated to reason about - we need typecasting
  and a new pi_dom*)
Variable keep_muts: mut_adt -> bool.
Definition keep_tys (gamma: context) : typesym -> bool :=
  fun ts =>
  match find_ts_in_ctx gamma ts with
  | Some (m, a) => keep_muts m
  | None => (*doesn't matter, not ADT*) true
  end.
(* Variable keep_tys : typesym -> bool. *)

(*NOTE: we parameterize by cc_map. In our case, this is the identity, but
  in principle it could be any map of new constructors*)
(*This could be from a map or it could e.g. the identity function*)
(*We only map to new names, we don't change the types (in real Why3, this is a clone)*)

Definition fpsym_clone (f: fpsym) (n: string) : fpsym :=
  Build_fpsym n (s_params f) (s_args f) (s_args_wf f) (s_params_nodup f).
  (*If cloned, not constr*)
Definition funsym_clone (f: funsym) (n: string) : funsym :=
  Build_funsym (fpsym_clone f n) (f_ret f) false 0 (f_ret_wf f).

(*Should it be funsym -> string or string -> string?*)
Variable (new_constr_name: funsym -> string).

(*Parameterize by no_ind, no_inv, no_sel*)
(*Ignore no_sel and no_inv - not used anywhere*)
Variable (noind: typesym -> bool).

Section Badnames.
(*We need to make sure new funsym names are unique*)
Variable badnames: list string.

Definition gen_id s := gen_name s badnames.

Definition n_str : string := "n".
Definition under_str : string := "_".

(*To disambiguate: prefix with n and put _ before numbers*)
Definition new_constr (f: funsym) : funsym := funsym_clone f (gen_id 
  (n_str ++ under_str ++ (new_constr_name f) ++ under_str)).


(*Generate axioms*)

Definition add_param_decl (t: task) (f: funsym) : task :=
  (abs_fun f :: task_gamma t, task_delta t, task_goal t).

Definition add_axiom (t: task) (n: string) (f: formula) : task :=
  (task_gamma t, (n, f) :: task_delta t, task_goal t).

(*In all of these, we separate out the definition of the axioms/funsyms and the
  "stateful" (in the monadic sense) function that updates the task and state*)



(*For inclusion of types, need type fixed. For nodup, we 
  call the nodup function on (ts_args ts). Since this arises from an adt,
  in a well-typed context, (ts_args ts = m_params m), which has nodups.
  But we prove this later because we don't use any context info*)

(*TODO: move*)
(* Lemma sublist_iff_r {A: Type} (l1 l2 l3: list A):
  (forall x, In x l2 -> In x l3) ->
  sublist l1 l2 ->
  sublist l1 l3.
Proof.
  intros Heq Hsub. intros x Hinx. auto.
Qed. *)

(*NOTE: here we fix ty to [vty_cons ts (map vty_var (ts_args ts))] (i.e. adt_ty ts),
  or else we cannot prove the type variable inclusion*)
(*TODO: reduce duplication*)
Lemma selector_check_args (ts: typesym) (csl: list funsym):
  let mt_var := gen_name "a" (ts_args ts) in
  let mt_ty : vty := vty_var mt_var in
  let ty := vty_cons ts (map vty_var (ts_args ts)) in
  let mt_al := ty :: rev_map (fun _ => mt_ty) csl in
(check_args (mt_var :: nodup string_dec (ts_args ts)) mt_al).
Proof.
  apply (reflect_iff _ _ (check_args_correct _ _)).
  intros x. simpl. intros [Hx | Hinx].
  - subst. simpl.
    apply sublist_cons. apply sublist_trans with (l2:=ts_args ts).
    + (*Just use induction, should prove*)
      induction (ts_args ts) as [| h t IH]; simpl; auto; [apply sublist_refl|].
      destruct (in_dec _ _ _); [apply sublist_cons|apply sublist_cons_l]; auto.
    + intros x. rewrite nodup_In. auto.
  - unfold rev_map in Hinx. rewrite <- In_rev, in_map_iff in Hinx.
    destruct Hinx as [f [Hf Hinf]]; subst. simpl.
    apply sublist_cons_l, sublist_nil_l.
Qed. 

Lemma selector_args_nodup (ts: typesym):
  let mt_var := gen_name "a" (ts_args ts) in
  nodupb typevar_eq_dec (mt_var :: nodup string_dec (ts_args ts)).
Proof.
  simpl.
  apply (reflect_iff _ _ (nodup_NoDup _ _)).
  constructor.
  - rewrite nodup_In. apply gen_name_notin.
  - apply NoDup_nodup.
Qed.

Lemma selector_ret_sublist (ts: typesym)  :
  let mt_var := gen_name "a" (ts_args ts) in
  let mt_ty : vty := vty_var mt_var in
  check_sublist (type_vars mt_ty) (mt_var :: nodup string_dec (ts_args ts)).
Proof.
  apply (reflect_iff _ _ (check_sublist_correct _ _)).
  simpl. apply sublist_cons_l, sublist_nil_l.
Qed.

Definition match_str : string := "match_".

Definition selector_name ts : string := (match_str ++ ts_name ts ++ under_str)%string.

Definition selector_funsym(ts: typesym) (csl: list funsym) : funsym :=
  let mt_id : string := gen_id (selector_name ts)  in
  let mt_var := gen_name "a" (ts_args ts) in
  let mt_ty : vty := vty_var mt_var in
  let ty := vty_cons ts (map vty_var (ts_args ts)) in
  (*Params: new name + all params in ts*)
  (*args are ty and then bunch of copies of mt_ty, 1 per constructor*)
  let mt_al := ty :: rev_map (fun _ => mt_ty) csl in
  Build_funsym (Build_fpsym mt_id (mt_var :: nodup string_dec (ts_args ts)) mt_al 
    (selector_check_args ts csl) (selector_args_nodup ts)) mt_ty false 0 (selector_ret_sublist ts).


(*The selector axiom for a given typesym and constructor list*)
(*NOTE: the cc_map is probably the identity map but we still keep it because
  it is not (for some reason) in the full version*)
(*TODO: need condition that all funsyms in csl appear in cc_map*)
Definition selector_axiom
  (ts: typesym) (*(ty: vty)*) (csl: list funsym) : funsym * list (string * formula) (*list (funsym * formula)?*) :=
  (*fix ty*)
  let ty := vty_cons ts (map vty_var (ts_args ts)) in
  (* declare the selector function *)
  let mt_id : string := gen_id (selector_name ts) in
  (*TODO: does it need to be fresh? Yes, cannot be in params of ts*)
  let mt_var := gen_name "a" (ts_args ts) in
  let mt_ty : vty := vty_var mt_var in
  (* let mt_ty = ty_var (create_tvsymbol (id_fresh "a")) in *)
  let mt_al := ty :: rev_map (fun _ => mt_ty) csl in
  (*Create with params START*)
  let mt_ls := selector_funsym ts csl in
  (* let mt_ls := funsym_noconstr_noty mt_id mt_al mt_ty in *)
  (* let mt_map2 := amap_set typesym_eq_dec s.(mt_map) ts mt_ls in *)
  (* define the selector function *)
  (*Generate new vars*)
  let varnames := gen_names (length csl) "z"%string nil in
  let mt_vl : list vsymbol := rev_map (fun x => (x, mt_ty)) varnames in
  (* let mt_vs _ = create_vsymbol (id_fresh "z") mt_ty in *)
  (* let mt_vl = List.rev_map mt_vs csl in *)
  let mt_tl := rev_map Tvar mt_vl in
  let mt_add (cs: funsym) t :=
    let id := (mt_id ++ under_str ++ (s_name cs))%string in
    (* let id = mt_ls.ls_name.id_string ^ "_" ^ cs.ls_name.id_string in *) 
    (* let pr = create_prsymbol (id_derive id cs.ls_name) in *)
    (*Create new vars - they can be the same among axioms (TODO: inefficient)*)
    let varnames2 := gen_names (length (s_args cs)) "u"%string varnames in
    let vl := rev (combine varnames2 (s_args cs)) in
    (* let vl = List.rev_map (create_vsymbol (id_fresh "u")) cs.ls_args in *)
    let newcs := new_constr cs in (*amap_get_def funsym_eq_dec cc_map cs id_fs in (*TODO: show have*)*)
    (*Typing: constr get ADT args*)
    let hd := Tfun newcs (map vty_var (ts_args ts)) (rev_map Tvar vl)  in
    (* let hd := tfun_infer' newcs (rev_map snd vl) (rev_map Tvar vl) in TODO: is return type right? - they say f_ret cs *)
    (*Typing: selector funsym has extra type arg (representing return type)
      just substitute with mt_ty (this is return type of whole funsyms)*)
    let hd := Tfun mt_ls (mt_ty :: (map vty_var (ts_args ts))) (hd :: mt_tl) in
    (* let hd := tfun_infer' mt_ls ((f_ret cs) :: map snd mt_vl) (hd :: mt_tl) in *)
    let vl := rev_append mt_vl (rev vl) in
    let ax := fforalls vl (Feq mt_ty hd t) in
    (id, ax)
  in 
  (mt_ls, map2 mt_add csl mt_tl).

(*INVARINT: mt_map is fst (selector_axiom)*)

Definition add_task_axioms (t: task) (axs: list (string * formula)) : task :=
  fold_left (fun acc x => add_axiom acc (fst x) (snd x)) axs t.

(*NOTE: will prob need to separate out for proof purposes (e.g. map2 vs fold_left2 and separate function)*)
Definition add_selector_aux (tsk: task) (ts: typesym) (csl: list funsym) :=
  (* if s.(no_sel) then (s, tsk) else *)
  let sel := selector_axiom ts csl in
  let mt_ls := fst sel in
  let axms := snd sel in
  let tsk := add_param_decl tsk mt_ls in
  let tsk := add_task_axioms tsk axms in
  (*update state*)
  (* let mt_map2 := amap_set typesym_eq_dec s.(mt_map) ts mt_ls in *)
  tsk.
  (* (s <|mt_map := mt_map2|>, tsk). *)

Definition single {A: Type} (l: list A) : bool :=
  match l with | [_] => true | _ => false
  end.

(*An informative one - this is nicer in proofs than pattern matching*)
Definition get_single {A: Set} (l: list A) :
  Either {x: A | l = [x]} (forall x, l <> [x]).
Proof.
  destruct l as [| h [| h1 t1]]; [apply Right | apply Left | apply Right].
  - intros x; discriminate.
  - apply (exist _ h). reflexivity.
  - intros x; discriminate.
Qed.

(*Don't need selector for types with single constructor because trivial.
  NOTE: does this cause any problems with eliminating singleton types (e.g. user defined tuple)
  need to see in rewriteT*)
Definition add_selector (acc : task) (ts: typesym) (x: list funsym) :
  task :=
  if single x then acc else  add_selector_aux acc ts x.

Definition mapi {A B: Type} (f: nat -> A -> B) (l: list A) : list B :=
  map (fun x => f (fst x) (snd x)) (combine (seq 0 (length l)) l).

(*Indexer funsym - similarly as selector, we fix the type for well-formed*)

Lemma indexer_check_args (ts: typesym) :
  let ty := vty_cons ts (map vty_var (ts_args ts)) in
  check_args (nodup typevar_eq_dec (ts_args ts)) [ty].
Proof.
  simpl. rewrite andb_true_r.
  apply (reflect_iff _ _ (check_sublist_correct _ _)).
  intros x Hinx. rewrite nodup_In. simpl_set. destruct Hinx as [y [Hiny Hinx]].
  rewrite in_map_iff in Hiny. destruct Hiny as [v [Hy Hinv]]; subst.
  simpl in Hinx. destruct Hinx as [Hxv | []]; subst; auto.
Qed.

Lemma nodupb_nodup {A: Type} eq_dec (l: list A):
  nodupb eq_dec (nodup eq_dec l).
Proof.
  apply (reflect_iff _ _ (nodup_NoDup _ _)), NoDup_nodup.
Qed.

(*Again, will prove nodup does nothing*)
Definition index_str := "index_"%string.
Definition indexer_name (ts: typesym) : string :=
  (index_str ++ (ts_name ts) ++ under_str)%string.

Definition indexer_funsym (ts: typesym) : funsym :=
  let ty := vty_cons ts (map vty_var (ts_args ts)) in
  let mt_id := gen_id (indexer_name ts) in
  Build_funsym (Build_fpsym mt_id (nodup typevar_eq_dec (ts_args ts)) [ty] 
    (indexer_check_args ts) (nodupb_nodup _ _)) vty_int false 0 eq_refl.


(*Again, define indexer axiom*)
Definition indexer_axiom
  (ts: typesym) (*(ty : vty)*) (csl : list funsym) : funsym * list (string * formula) :=
  (* declare the indexer function *)
  let mt_id := gen_id (indexer_name ts) in
  let mt_ls := indexer_funsym ts in (*funsym_noconstr_noty mt_id [ty] vty_int in*)
  (* define the indexer function *)
  let mt_add idx (cs: funsym) :=
    let id := (mt_id ++ under_str ++ (s_name cs))%string in
    (* let pr = create_prsymbol (id_derive id cs.ls_name) in *)
    let varnames := gen_names (length (s_args cs)) "u" nil in
    let vl := rev (combine varnames (s_args cs)) in
    let newcs := new_constr cs (*amap_get_def funsym_eq_dec cc_map cs id_fs in*) in
    (*NOTE: THESE TYPES MAY BE WRONG!*)
    (*Types: newcs has constr type, apply args, just use params*)
    let hd := Tfun newcs (map vty_var (ts_args ts)) (rev_map Tvar vl) in
    (* let hd := tfun_infer' newcs (rev (map snd vl)) (rev_map Tvar vl) in *)
    (* let hd = fs_app newcs (List.rev_map t_var vl) (Option.get cs.ls_value) in *)
    (*Types: mt_ls has type (e.g. list a -> int), apply to type (list a), again
      use params*)
    let ax := Feq vty_int (Tfun mt_ls (map vty_var (ts_args ts)) [hd])
    (* tfun_infer' mt_ls [(f_ret newcs)] [hd] )   *)
      (Tconst (ConstInt (Z.of_nat idx))) in
    let ax := fforalls (rev vl) ax in
    (id, ax) in
  (mt_ls, mapi mt_add csl). 

Definition add_indexer_aux (tsk: task) (ts: typesym) (*(ty : vty)*) (csl : list funsym) : task :=
  let indexer := indexer_axiom ts csl in
  let mt_ls := fst indexer in
  let axms := snd indexer in
  (*update task*)
  let tsk := add_param_decl tsk mt_ls in
  let tsk := add_task_axioms tsk axms in
  tsk.

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
Definition discriminator_axioms (ts: typesym) (ty: vty) (csl: list funsym) : 
  list (string * formula) :=
  let d_add (c1: funsym) (c2: funsym) : (string * formula) :=
    let i : string := gen_id ((s_name c1) ++ "_" ++ (s_name c2))%string in
    (* let pr = create_prsymbol (id_derive id ts.ts_name) in *)
    (*Create vars - TODO: does it have to be fresh against some vars?*)
    let ul := rev (combine (gen_names (length (s_args c1)) "u" nil) (s_args c1)) in
    let vl := rev (combine (gen_names (length (s_args c2)) "v" nil) (s_args c2)) in
    (* let ul := rev_map (create_vsymbol (id_fresh "u")) c1.ls_args in
    let vl = List.rev_map (create_vsymbol (id_fresh "v")) c2.ls_args in *)
    let newc1 := new_constr c1 in (*amap_get_def funsym_eq_dec (cc_map) c1 id_fs in*)
    let newc2 := new_constr c2 in (*amap_get_def funsym_eq_dec (cc_map) c2 id_fs in*)
    (*Types: constr, apply to constr, given args, so just give params
      Important that both constrs are in  *)
    let t1 := Tfun newc1 (map vty_var (ts_args ts)) (rev_map Tvar ul) in
    let t2 := Tfun newc2 (map vty_var (ts_args ts)) (rev_map Tvar vl) in
    (* let t1 := tfun_infer' newc1 (rev (map snd ul)) (rev_map Tvar ul) in
    let t2 := tfun_infer' newc2 (rev (map snd vl)) (rev_map Tvar vl) in *)
    (* let t1 = fs_app newc1 (List.rev_map t_var ul) ty in
    let t2 = fs_app newc2 (List.rev_map t_var vl) ty in *)
    let ax := t_neq ty t1 t2 in
    let ax := fforalls (rev vl) ax in
    let ax := fforalls (rev ul) ax in
    (i, ax)
  in
  map_pairs d_add csl.


Definition add_discriminator (tsk: task) (ts: typesym) (ty: vty) (csl: list funsym) : task :=
  let axs := discriminator_axioms ts ty csl in
  add_task_axioms tsk axs.

(*TODO: see if we want to do this still - are there types with more than 16 constructors?*)
Definition add_indexer (acc: task) (ts: typesym) (ty: vty) (cs: list funsym) := 
  if single cs then acc else
  if negb (noind ts) then add_indexer_aux acc ts cs
    else if Nat.leb (length cs) 16 then add_discriminator acc ts ty cs 
    else acc.

Lemma dep_mapi_forall {A B: Type} {P} {l1: list A} {l2: list B}: 
  Forall P l2 ->
  Forall (fun x => P (snd x)) (combine l1 l2).
Proof.
  revert l1. induction l2 as [| h t IH]; simpl; intros [| h1 t1]; simpl; auto.
  intros Hall. inversion Hall; subst. constructor; auto.
Qed.

Definition dep_mapi {A B: Type} (P: A -> Prop) (f: nat -> forall (x: A), P x -> B)
  (l: list A) (Hall: Forall P l) : list B :=
  dep_map (fun x => f (fst x) (snd x)) (combine (seq 0 (length l)) l)
  (dep_mapi_forall Hall).

(*NOTE: complete_projections just copies over projections if they exist.
  We do not have any projections in our data, so we only implement the "None" case.
  TODO: we will need a predicate/typing rule asserting that projection is correct if it exists
  or something (not sure exactly what we need - will certainly need typing info) *)
(*ONLY creates function symbols - so projections are just user-named functions essentially - spec should
  just be that this produces SOME function symbol of the right type*)
(*TODO: START: define params explicitly, need to prove for types of args and ret - so need
  dependent mapi - ty is in s_args (or carry around Hall hypothesis)*)
(*TODO: is this computable now? Does it matter?*)

(*We need to prove the nodup, sublist, etc for the projection symbols. The argument is always
  [f_ret c] and the return type is one of [s_args c], so we can always give the params of c
  (and it is important later that we do so; it might have extra params but this is OK)*)

(*Prove 3 obligations*)
Lemma check_args_ret (c: funsym):
  check_args (s_params c) [f_ret c].
Proof.
  simpl. rewrite andb_true_r.
  destruct c; simpl. auto.
Qed.

Lemma in_args_check_sublist (c: funsym) (ty: vty) (Hty: In ty (s_args c)):
  check_sublist (type_vars ty) (s_params c).
Proof.
  destruct c; simpl in *. 
  destruct f_sym; simpl in *.
  unfold is_true in s_args_wf.
  rewrite <- (reflect_iff _ _ (check_args_correct _ _)) in s_args_wf. unfold is_true.
  rewrite <- (reflect_iff _ _ (check_sublist_correct _ _)).
  auto.
Qed.

Definition proj_funsym (c: funsym) (n: string) (ty: vty) (Hty: In ty (s_args c)) : funsym :=
  Build_funsym (Build_fpsym n (s_params c) [f_ret c] (check_args_ret c) (s_params_nodup c)) 
    ty false 0 (in_args_check_sublist c ty Hty).

Definition p_str : string := "p".
Definition proj_str : string := "_proj_".

Definition projection_syms (c: funsym) : list funsym :=
  let conv_p (i: nat) (ty: vty) (Hty: In ty (s_args c)) :=
    let id := gen_id (p_str ++ (s_name c) ++ proj_str ++ (nat_to_string i) ++ under_str)%string in
    proj_funsym c id ty Hty
    (* TODO: do we need option?(funsym_noconstr_noty id [f_ret c] ty) *)
  in
  dep_mapi _ conv_p (s_args c) (all_in_refl _).

Definition complete_projections (csl: list funsym) : list (funsym * list funsym) :=
  map (fun c => (c, projection_syms c)) csl.

(*Projection axioms*)
(*We do NOT thread cp_map, pp_map*)

(*What to do about [pp_map] - we do not have old projections.
  Also we never access pp_map outside of this function - useless to us *)
(*We consider projection axioms for a single constructor and list of projection symbols
  (given by [projection_names]) - pj_add from before*)
Definition projection_axioms
  (cs: funsym) (pl: list funsym) : list (funsym * (string * formula)) :=
  (* declare and define the projection functions *)
  (*Fresh vars TODO*)
  let vl := combine (gen_names (length (s_args cs)) "u" nil) (s_args cs) in
  (* let vl = List.map (create_vsymbol (id_fresh "u")) cs.ls_args in *)
  let tl := map Tvar vl in
  (*Types: new_constr has type (e.g. a -> list a -> list a),
    should instantiate w (map vty_var (s_args c))*)
  let hd := Tfun (new_constr cs) (map vty_var (s_params cs)) tl in
  (*let hd := tfun_infer' (new_constr cs) (*(amap_get_def funsym_eq_dec (cc_map) cs id_fs)*)
    (map snd vl) tl in*)
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
    (*Types: ls is projection, has type (e.g. cons a -> a),
      we apply to [hd], which has type e.g. list a - just give params*)
    let hh := Tfun ls (map vty_var (s_params cs)) [hd] in
    (* let hh := tfun_infer' ls [(f_ret cs)] [hd] in *)
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
Definition add_projections {A B: Type} (tsk: task) (_ts : A) (_ty : B) (csl: list funsym) :
  task :=
  (*For each constructor, get projections and axioms, add projection funsym and axioms to task*)
  (*Do in 2 pieces: order doesn't matter because one affects gamma, the other affects delta*)
  let tsk := fold_left (fun acc c => 
    let projs := projection_axioms c (projection_syms c) in
    fold_left (fun tsk x => 
      let pj := fst x in
      let ax := snd x in
      add_axiom (add_param_decl tsk pj) (fst ax) (snd ax) 
    ) projs acc
    ) csl tsk in
  (*update state with projections - should be just rev (projection_syms) (TODO make sure)*)
  (* let cp_map2 := fold_left (fun acc x => amap_set funsym_eq_dec acc x (rev (projection_syms x))) csl s.(cp_map) in *)
  (* let st := s <| cp_map := cp_map2 |> in *)
  tsk.

(*TODO: do we need state at all (other than maybe constructor map) - we know exactly what is
  in the state for each - really should just need task*)

Definition inversion_axiom
  (ts: typesym) (ty: vty) (csl: list funsym) : string * formula :=
  (* add the inversion axiom *)
  let ax_id := ((ts_name ts) ++ "_inversion")%string in
  (* let ax_pr = create_prsymbol (id_derive ax_id ts.ts_name) in *)
  (*TODO: fresh?*)
  let ax_vs := (gen_name "u"%string nil, ty) in 
  let ax_hd := Tvar ax_vs in
  let mk_cs (cs: funsym) : formula :=
    (*NOTE: we know the pjl from the projections*)
    let pjl := projection_syms cs in
    (* let pjl := amap_get_def funsym_eq_dec s.(cp_map) cs nil in  *)
    (*Types: projection type is list a b -> (type of ith)
      ty is (list a b) arg is same type, so just need ts_params as arguments*)
    let app pj := Tfun pj (map vty_var (ts_args ts)) [ax_hd] in

    (*NOTE: change app to also give return type*)
    (* let app pj := tfun_infer_ret' pj [ty] [ax_hd] in *)
    (* let app pj = t_app_infer pj [ax_hd] in *)
    let cs := new_constr cs (*amap_get_def funsym_eq_dec cc_map cs id_fs in*) in
    (* let cs = Mls.find cs state.cc_map in *)
    let pjl' := map app pjl in
    (*Types: doing: cons (proj1 x, proj2 x). The type args should again by (ts_args ts)*)
    Feq ty ax_hd (Tfun cs (map vty_var (ts_args ts)) pjl')
    (* (tfun_infer' cs (map snd pjl') (map fst pjl'))*)
    (* t_equ ax_hd (fs_app cs (List.map app pjl) ty) in *)
  in
  let ax_f := map_join_left' Ftrue mk_cs (Fbinop Tor) csl in
  let ax_f := Fquant Tforall ax_vs ax_f (*t_forall_close [ax_vs] [] ax_f in*) in
  (ax_id, ax_f).


Definition add_inversion (tsk: task) (ts: typesym) (ty: vty) (csl: list funsym) :
  task :=
  (* if s.(no_inv) then st else *)
  let inv := inversion_axiom ts ty csl in
  add_axiom tsk (fst inv) (snd inv).

(*TODO: since we don't have builtin projections, we can't do the
  [kept_no_case] part for projections. We don't implement it at all.
  TODO: need to figure out: do we prove only a subset of allowed behaviors sound?
  or can we prove the rest at the higher level - assuming something about projections, etc
  Or should we add projections? Need to figure this out!*)

Definition add_param_decls (l: list funsym) (tsk: task) : task :=
  fold_left add_param_decl l tsk.

Definition adt_ty (ts: typesym) : vty := vty_cons ts (map vty_var (ts_args ts)).

Definition add_axioms (tsk: task) (d: typesym * list funsym) : task :=
  let ts := fst d in
  let csl := snd d in
  (*NOTE: might be very easy to infer all types - might not need infer, might just all be typesym args*)
  let ty := adt_ty ts in
  (*TODO: SKIP KEPT_NO_CASE*)
  (*Just add axioms for all maybe?*)
  (*if negb (null (ts_args ts)) (*|| negb (amap_mem typesym_eq_dec ts s.(kept_m))*) then*)
  (* declare constructors as abstract functions *)
  let tsk := add_param_decls (map new_constr csl) tsk in
  (* let st := (s, tsk) in *)
    (*let cs_add (st: state * task) (cs: funsym) :=
      let s := fst st in let tsk := snd st in
      (s <| cc_map := amap_set funsym_eq_dec s.(cc_map) cs (new_constr cs) |>, 
        add_param_decl tsk (new_constr cs))
      (* let id := s_name cs in (*TODO: no clone, is this ok*)
      let ls := funsym_noconstr_noty id (s_args cs) (f_ret cs) in (*TODO: this is ls*)
      (* let ls = create_lsymbol id cs.ls_args cs.ls_value in *)
      (s <| cc_map := amap_set funsym_eq_dec s.(cc_map) cs ls |>, add_param_decl tsk ls) *)
      (* { state with cc_map = Mls.add cs ls state.cc_map },add_param_decl task ls *)
  in
  let st := fold_left cs_add csl st in*)
  (* add selector, projections, and inversion axiom *)
  let tsk := add_selector tsk ts csl in
  let tsk := add_indexer tsk ts ty csl in
  let tsk := add_projections tsk ts ty csl in
  add_inversion tsk ts ty csl.
  (*else st.*)

(*Skip [add_tags] and finding infinite types - only deals with metas*)

(*rewriting*)


Section Rew.
Variable (gamma: context).
(* Variable (s: state). *)
(*We do use a map for selectors (for now)*)
(*We parameterize by a function, instantiate with looking up in context
  (much easier in proofs than using state)*)

(*We can define the function giving [mt_map]*)

Definition get_mt_map (t: typesym) : funsym :=
  match (find_ts_in_ctx gamma t) with
  | Some (m, a) => fst (selector_axiom t (adt_constr_list a))
  | _ => id_fs
  end.

(*TODO: bad, can we find the type differently?*)
Definition pat_match_ty (pats: list (pattern * term)) : option vty :=
  match pats with
  | nil => None
  | (p, t) :: _ => Typechecker.typecheck_term gamma t
  end.
Definition pat_match_ty' pats :=
  match pat_match_ty pats with
  | Some t => t
  | _ => vty_int
  end.


(*Assume we have a list of banned variables (instantiate with term vars)*)
Variable badvars : list vsymbol.

(*It is often difficult to figure out what the type arguments for functions should be.
  We will do it as they do, trying to instantiate a type mapping*)

(*Don't use state, use functional view of projection symbols*)
(*A functional version of the projection function symbol*)


(*Then, the function giving the projection symbols for a function is:*)
(*NOTE: changed to [fold_right], so not rev anymore*)
Definition get_proj_list (c: funsym) : list funsym :=
  (*(rev*) (projection_syms c)(*)*).

Definition enc_ty (t: vty) : bool :=
  match t with
  | vty_cons ts _ => negb (keep_tys gamma ts)
  | _ => false
  end.

(*Separate rewriteT/F (pat match case) into multiple functions to
  make it easier to reason about*)
  (*Idea: for a given constructor, gives term (ex:)
  match l with
  x :: t -> f (x, t) 
  becomes
  let x := proj_cons_1(l) in let t := proj_cons_2(l) in f(x, t)
  in map m, maps cons -> (let x := ...)
  in w, set if there is a wild or not - if there is wild, gives term
  *)
(*Note: change fold_left2' to map and then fold_let so easier to prove*)
Definition fold_let {A: Type} (tlet: term -> vsymbol -> A -> A)
  (l: list (term * vsymbol)) (b: A) : A :=
  fold_right (fun x acc => tlet (fst x) (snd x) acc) b l.

Definition mk_br_tm (rewriteT: term -> term) (args: list vty)  t1
  (x: option term * amap funsym term) (br: pattern * term) :=
  let w := fst x in
  let m := snd x in
  let e := rewriteT (snd br) in
  match (fst br) with
  | Pconstr cs tys pl =>
    let add_var p pj :=
      match p with
      | Pvar v => (Tfun pj args [t1], v)
      | _ => (tm_d, vs_d) (*NOTE: default, because we never hit it anyway by assumption*)
      end
      in
      let pjl := get_proj_list cs (*amap_get_def funsym_eq_dec s.(cp_map) cs nil*) in 
        (*match amap_get funsym_eq_dec s.(cp_map) cs with
      | Some cp => cp
      | None => nil (*TODO: prove don't hit (basically, will prove by knowing that all
        defined types appeared before and hence have already been added to map)*)
      end in*)
      let e := fold_let Tlet (map2 add_var pl pjl) e in
      (* let e := fold_left2' add_var pl pjl e in *)
      (w, amap_set funsym_eq_dec m cs e)
  | Pwild => (Some e, m)
  | _ => (*Prove don't hit*) x
  end.

(*TODO: generalize?*)
Definition mk_brs_tm (rewriteT: term -> term) (args: list vty) (t1: term) (pats: list (pattern * term)) :=
  fold_left (mk_br_tm rewriteT args t1) pats (None, amap_empty).

(*And formula case*)
(*Note: stores juts pattern list info:
  ex: cons -> ([h;t], 1 + length t)*)
Definition mk_br_fmla (rewriteF: formula -> formula)
  (x: option formula * amap funsym (list vsymbol * formula)) (br: pattern * formula) :=
    let p := fst br in
    let e := snd br in
    let w := fst x in
    let m := snd x in
    let e := rewriteF e in (*rewriteF av' sign e in*)
    match p with
    | Pconstr cs tys pl =>
      let get_var p : vsymbol := match p with
        | Pvar v => v
        | _ => (*TODO: prove don't hit*) vs_d
      end in
      (w, amap_set funsym_eq_dec m cs (map get_var pl, e))
    | Pwild => (Some e, m)
    | _ => (*TODO: prove dont hit*) x
    end .

Definition mk_brs_fmla (rewriteF: formula -> formula) (pats : list (pattern * formula) ) :=
  fold_left (mk_br_fmla rewriteF) pats (None, amap_empty).

(*Instead of matching on t1 to find var, have custom informative match to give only 2 cases*)
Definition is_tm_var (t: term) :
  Either {v: vsymbol | t = Tvar v} (forall v, t <> Tvar v).
Proof.
  destruct t; try solve[apply Right; intros; discriminate].
  apply Left. apply (exist _ v). apply eq_refl.
Defined.

(*Kind of silly, but separate out default case so dont have to prove twice*)
Definition rewriteF_default_case ty1 t1 (sign: bool) vl hd e : formula :=
  let hd := Feq ty1 t1 hd (*TODO: ty1?*) in if sign then fforalls vl (Fbinop Timplies hd e)
    else fexists vl (Fbinop Tand hd e).

(*Also separate out [find]*)
Definition rewriteF_find (t1: term) (ty1: vty) (args: list vty) (av: list vsymbol) (sign: bool)
  (m: amap funsym (list vsymbol * formula))
  (w: option formula) (cs: funsym) : 
  formula :=
  let res := match amap_get funsym_eq_dec m cs with
  | Some y => y
  | None => (*Need fresh vars - TODO: *)
      (*If wild, we give fresh vars w1, w2 then wild value
        vars need correct type - it is just (ty_subst (s_params c) args (s_args c))
        (TODO make sure)*)
      (* let projs := get_proj_list cs (*amap_get_def funsym_eq_dec (s.(cp_map)) cs nil*) in *)
      (*NOTE: this is going to be very difficult to show, relies on lots of well-typing*)
      let names := gen_strs (length (s_args cs)) badvars in
      let tys := ty_subst_list (s_params cs) args (s_args cs) in
      let vars := combine names tys : list vsymbol in
      
      (*NOTE: I think type should be ty_subst (s_params s) [ty1] (s_ret s) - they use t_app_infer*)
      (* let vars := map2 (fun n (p: funsym) => (n, ty_subst (s_params p) [ty1] (f_ret p))) names projs : list vsymbol in *)
      (vars, match w with | Some y => y | None => Ftrue end) (*TODO: prove dont hit*)
  end
  in
  let vl := fst res in let e := snd res in
  (*NOTE: use args here*)
  let hd := Tfun (new_constr cs) args (map Tvar vl) in
  (* tfun_infer' (new_constr cs) (*(amap_get_def funsym_eq_dec (s.(cc_map)) cs id_fs)*) (map snd vl) (map Tvar vl) in *)
  match (is_tm_var t1) with
  | Left s =>
    let v := proj1_sig s in
    if in_dec vsymbol_eq_dec v av then
    let hd := Flet hd v e in if sign then fforalls vl hd else fexists vl hd
    else
    rewriteF_default_case ty1 t1 sign vl hd e 
    (* let hd := Feq ty1 t1 hd (*TODO: ty1?*) in if sign then fforalls vl (Fbinop Timplies hd e)
    else fexists vl (Fbinop Tand hd e) *)
  | Right _ =>
    rewriteF_default_case ty1 t1 sign vl hd e
    (* let hd := Feq ty1 t1 hd (*TODO: ty1?*) in if sign then fforalls vl (Fbinop Timplies hd e)
    else fexists vl (Fbinop Tand hd e) *)
  end.


Fixpoint rewriteT (t: term) : term :=
  match t with
  | Tmatch t1 ty pats => 
    if enc_ty ty then
      let t1 := rewriteT t1 in
      (*By typing, has to be an ADT*)
      let ts := match ty with | vty_cons ts _ => ts | _ => ts_d (*impossible*) end in
      let args := match ty with | vty_cons _ args => args | _ => nil (*impossible*) end in
      let res := mk_brs_tm rewriteT args t1 pats in
      let w := fst res in
      let m := snd res in (*gives map constructors to new terms*)
      (*find: for each constructor, get the term, if the term is not there,
        get wild info (NOTE: cannot be None by exhaustiveness)*)
      let find x := 
        match amap_get funsym_eq_dec m x with
        | Some e => e
        | None => match w with | Some x => x | None => (*impossible*) tm_d end
        end
      in
     
      let tl := map find (get_constructors gamma ts) in
      match (get_single tl) with 
      | Left x => proj1_sig x
      | Right _ =>
        (*Types: return type is foo a b c ... -> a1 -> a1 -> a1 (a1 is first param)
          We apply this to t1 (which has type ts(args), which must (adt_name a) args)
          so the type arguments should be (type of return) :: args
          type of return is not present in here, unfortunately, so we use [pat_match_ty]*)
        Tfun (get_mt_map ts) (pat_match_ty' pats :: args) (t1 :: tl)
      end
    else t_map rewriteT (rewriteF nil true) t
  | Tfun ls tys args => (*map old constrs to new constr*)
    if ls.(f_is_constr) && enc_ty (f_ret ls) (*we can just pass in return type because only depends on typesym*)
    then Tfun (new_constr ls) (*(amap_get_def funsym_eq_dec s.(cc_map) ls id_fs)*) tys 
      (map rewriteT args)
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
      (* let mk_br (x: option formula * amap funsym (list vsymbol * formula)) br :=
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
        end in *)
      let res := mk_brs_fmla (rewriteF av' sign) pats in
      let w := fst res in
      let m := snd res in
      (*By typing, has to be an ADT*)
      let ts := match ty1 with | vty_cons ts _ => ts | _ => ts_d (*impossible*) end in
      let args := match ty1 with | vty_cons _ args => args | _ => nil (*impossible*) end in
      (* let find cs :=
        let res := match amap_get funsym_eq_dec m cs with
        | Some y => y
        | None => (*Need fresh vars - TODO: *)
            (*If wild, we give fresh vars w1, w2 then wild value
              vars need correct type - it is just (ty_subst (s_params c) args (s_args c))
              (TODO make sure)*)
            (* let projs := get_proj_list cs (*amap_get_def funsym_eq_dec (s.(cp_map)) cs nil*) in *)
            (*NOTE: this is going to be very difficult to show, relies on lots of well-typing*)
            let names := gen_strs (length (s_args cs)) badvars in
            let tys := ty_subst_list (s_params cs) args (s_args cs) in
            let vars := combine names tys : list vsymbol in
            
            (*NOTE: I think type should be ty_subst (s_params s) [ty1] (s_ret s) - they use t_app_infer*)
            (* let vars := map2 (fun n (p: funsym) => (n, ty_subst (s_params p) [ty1] (f_ret p))) names projs : list vsymbol in *)
            (vars, match w with | Some y => y | None => Ftrue end) (*TODO: prove dont hit*)
        end
        in
        let vl := fst res in let e := snd res in
        (*NOTE: use args here*)
        let hd := Tfun (new_constr cs) args (map Tvar vl) in
        (* tfun_infer' (new_constr cs) (*(amap_get_def funsym_eq_dec (s.(cc_map)) cs id_fs)*) (map snd vl) (map Tvar vl) in *)
        match t1 with
        | Tvar v => if in_dec vsymbol_eq_dec v av then
          let hd := Flet hd v e in if sign then fforalls vl hd else fexists vl hd
          else
          let hd := Feq ty1 t1 hd (*TODO: ty1?*) in if sign then fforalls vl (Fbinop Timplies hd e)
          else fexists vl (Fbinop Tand hd e)
        | _ => let hd := Feq ty1 t1 hd (*TODO: ty1?*) in if sign then fforalls vl (Fbinop Timplies hd e)
          else fexists vl (Fbinop Tand hd e)
        end
      in *)
      (* let ts :=
        match ty1 with | vty_cons ts _ => ts | _ => ts_d end (*TODO: show dont hit*) in *)
      let op := if sign then (Fbinop Tand) else (Fbinop Tor) in
      map_join_left' Ftrue (rewriteF_find t1 ty1 args av sign m w) op (get_constructors gamma ts)
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

Definition rewriteT' gamma t :=
  rewriteT gamma ((tm_fv t) ++ (tm_bnd t)) t.
Definition rewriteF' gamma x y f :=
  rewriteF gamma ((fmla_fv f) ++ (fmla_bnd f)) x y f.

Definition add_def (d: def) (t: task) : task :=
  (d :: task_gamma t, task_delta t, task_goal t).

(*Add mut with params from given mut and list of ADTs (should be subset)*)
Definition add_mut (m: mut_adt)(tys: list alg_datatype) (t: task) : task :=
  add_def (datatype_def (mk_mut tys (m_params m) (m_nodup m))) t.

(*NOTE: adding context here because we want a uniform context for [rewriteT']*)
Definition comp_ctx (gamma: context) (d: def) (tsk: task) : task :=
  (* let s := fst st in let tsk := snd st in *)
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
    (*All types are either abstract or concrete*)
    (*JOSH: made it fold_right to keep same order as context - should change in real version too*)
    let tsk := if (keep_muts m) then add_def d tsk else 
      List.fold_right (fun a t => add_ty_decl t (adt_name a)) tsk dl
    in
    (*let '(dl_concr, dl_abs) := partition (fun a => keep_tys (adt_name a)) dl in
    (*TODO: this does NOT preserve order, but keeps a well-typed permutation, see if this is problem*)
    let tsk := List.fold_left (fun t a => add_ty_decl t (adt_name a)) dl_abs tsk in
    let tsk := if null dl_concr then tsk else add_mut m dl_concr tsk in*)
    (* add needed functions and axioms *)
    let st := List.fold_left add_axioms (map (fun a => (adt_name a, adt_constr_list a)) dl) tsk in
    (* add the tags for infinite types and material arguments *)
    (* let mts := List.fold_right (fun '(t,l) => Mts.add t l) dl amap_empty in
    let st := List.fold_left (add_tags mts) st dl in *)
    (* return the updated state and task *)
    st
  | _ => 
    (*rewriting case*)
    (*TODO: should it be task_gamma tsk instead of separate gamma? prob*)
    add_def (TaskGen.def_map (rewriteT' gamma) (rewriteF' gamma nil true) d) tsk
  end.

(*And for formula (easy)*)
(* Definition comp_fmla (f: formula) (st: state * task) : state * task :=
let s := fst st in let tsk := snd st in
  (s, add_def (TaskGen.def_map (rewriteT' (task_gamma tsk) s) (rewriteF' (task_gamma tsk) s nil true) d) tsk). *)

(*NOTE: we use [fold_right] because our contexts are reverse-ordered
  There may be incompatibility with why3, or they may just be reversing twice.
  But for our typing, it is very important that the resulting context is still
  well-ordered*)
Definition fold_all_ctx (t: task) : task :=
  fold_right (comp_ctx 
    (task_gamma t)) (nil, task_delta t, task_goal t) (task_gamma t).

End Badnames.

(*Instantiate badnames with syms in context*)

(*Fold version - dont use Trans.fold, easier to manually thread state through*)
Definition fold_comp : trans :=
  fun t => 
  (*TODO: we CANNOT fold over t - should be empty task I believe (at least empty gamma)*)
    (*NEED to start from empty context and build up defs - TODO: do we need to reverse result?*)
    let badnames := idents_of_context (task_gamma t) in (*NOTE: easier to prove with*)
    let tsk1 := fold_all_ctx badnames t in
    (*NOTE: HAS to be (task_gamma t) here when we do this way - or else
      nothing has constructors (if eliminate all types
      this is because we are folding whole context at once instead of
      doing each definition and then task (NOTE: this is a substantive difference
      from theirs!))*)
    let del1 := map (rewriteF' badnames (task_gamma t) nil true) (map snd (task_delta tsk1)) in
    let g1 := rewriteF' badnames (task_gamma t) nil true (task_goal tsk1) in
    [(task_gamma tsk1, (combine (map fst (task_delta tsk1)) del1), g1)]. 

(*No infinte types or anything so just give state*)

Section FullTrans.


(*I suppose we could make all params, but prob not*)
(* Definition empty_state : state := {| mt_map := amap_empty; (*cc_map := amap_empty;*)
  cp_map := amap_empty; (*pp_map := amap_empty;*) (*no_ind := noind; no_inv := noinv; no_sel := nosel*)|}. *)


Definition eliminate_match : trans :=
  compose_trans compile_match fold_comp.

(*Note that compile_match is the same - with extra meta stuff we don't care about*)

Definition eliminate_algebraic : trans :=
  compose_trans compile_match fold_comp.

End FullTrans.

End ElimADT.

