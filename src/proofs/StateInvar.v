(*Here we give the invariants on the state*)
Require Import TransDefs.

Definition full_st : Type := Z * (hashcons_full).

Definition full_ctr (s: full_st) : Z := fst s.
Definition full_ty_hash (s: full_st) : hashcons_ty ty_c := fst (fst (fst (snd s))).
Definition full_decl_hash (s: full_st) : hashcons_ty decl := snd (fst (fst (snd s))).
Definition full_tdecl_hash (s: full_st) : hashcons_ty tdecl_c := snd (fst (snd s)).
Definition full_task_hash (s: full_st) : hashcons_ty task_hd := snd (snd s).

(*1. All variable identifiers in the task are < the value of the state*)
(*NOTE: could strengthen to all global ids (var, tyvar, lsymbol, type symbol),
  for now we do not. Our maps do not actually rely on injectivity of tags.
  (TODO: see if we need)*)

Section Idents.

(*Ignore set of vars, for well-typed, those should be found in pattern anyway*)
Fixpoint idents_of_pattern (p: pattern_c) : list ident :=
  match (pat_node_of p) with
  | Pvar v => [vs_name v]
  | Papp c ps => concat (map idents_of_pattern ps)
  | Por p1 p2 => idents_of_pattern p1 ++ idents_of_pattern p2
  | Pas p v => vs_name v :: idents_of_pattern p
  | Pwild => nil
  end.

(*Similarly, ignore [bind_info]*)

Fixpoint idents_of_term (t: term_c) : list ident :=
  match (t_node_of t) with
  | Tvar v => [vs_name v]
  | Tconst _ => nil
  | Tapp l ts => concat (map idents_of_term ts)
  | Tif t1 t2 t3 => idents_of_term t1 ++ idents_of_term t2 ++ idents_of_term t3
  | Tlet t1 (v, _, t2) => vs_name v :: idents_of_term t1 ++ idents_of_term t2
  | Tcase t1 ps => idents_of_term t1 ++ concat (map (fun x => idents_of_pattern (fst (fst x)) ++ idents_of_term (snd x)) ps)
  | Teps (v, _, t) => (vs_name v) :: idents_of_term t
  | Tquant q (vs, _, _, t)  => (*ignore triggers*) map vs_name vs ++ idents_of_term t
  | Tbinop _ t1 t2 => idents_of_term t1 ++ idents_of_term t2
  | Tnot t => idents_of_term t
  | _ => nil
  end.


(*Only need to worry about recun and indpred*)
Definition idents_of_logic_decl (l: logic_decl) : list ident :=
  idents_of_term (snd (fst (snd l))).

Definition idents_of_ind_list (i: ind_list) : list ident :=
  concat (map (fun x => concat (map idents_of_term (map snd (snd x)))) (snd i)).

Definition idents_of_decl_node (d: decl_node) : list ident :=
  match d with
  | Dlogic l => concat (map idents_of_logic_decl l)
  | Dind i => idents_of_ind_list i
  | Dprop p => idents_of_term (snd p)
  | _ => nil
  end.

(*Assume all Use, Clone compiled away*)
Definition idents_of_tdecl (t: tdecl_c) : list ident :=
  match (td_node_of t) with
  | Decl d => idents_of_decl_node (d_node d)
  | _ => nil
  end.

(*Task*)

Definition list_of_option {A B: Type} (f: A -> list B) (o: option A) : list B :=
  match o with
  | None => nil
  | Some y => f y
  end.
Definition list_of_option_id {A: Type} (o: option A) : list A :=
  list_of_option (fun x => [x]) o.

Fixpoint idents_of_task (t: task_hd) : list ident :=
  idents_of_tdecl (task_decl t) ++
    list_of_option idents_of_task (task_prev t).

(*The wf condition*)

Definition idents_of_task_wf  (o: option task_hd) (s : full_st) : Prop :=
  forall i, In i (list_of_option idents_of_task o) -> (id_tag i < (fst s))%Z.


End Idents.
(*2. All AST nodes in the task are in the corresponding hash table
  AND have tag < the corresponding hashcons counter*)
Section HashCons.

(*Hashconsed ASTs: type, decl, tdecl, task_hd - we provide functions to get
  all such instances from a task and then we can write our predicates*)

(*We want all subterms of type ty_c also. But we can just map this over at the end*)
Fixpoint tys_of_ty (t: ty_c) : list ty_c :=
  t :: match ty_node_of t with
       | Tyapp _ tys => concat (map tys_of_ty tys)
       | _ => nil
        end.

Definition tys_of_lsym (l: lsymbol) : list ty_c :=
  (list_of_option_id (ls_value l)) ++ ls_args l.

(*Again, ignore in Svs.t because in well-typed, already in pattern*)
Fixpoint tys_of_pat (p: pattern_c) : list ty_c :=
  pat_ty_of p ::
  match (pat_node_of p) with
  | Pvar v => [vs_ty v]
  | Papp l ps => tys_of_lsym l ++ concat (map tys_of_pat ps)
  | Por p1 p2 => tys_of_pat p1 ++ tys_of_pat p2
  | Pas p v => vs_ty v :: tys_of_pat p
  | Pwild => nil
  end.

(*NOTE that there will be redundancy; e.g. in let, type of vsymbol should be same as first term*)
Fixpoint tys_of_term (t: term_c) : list ty_c :=
  list_of_option_id (t_ty_of t) ++
  match t_node_of t with
  | Tvar v => [vs_ty v]
  | Tconst _ => nil
  | Tapp l tms => tys_of_lsym l ++ concat (map tys_of_term tms)
  | Tif t1 t2 t3 => tys_of_term t1 ++ tys_of_term t2 ++ tys_of_term t3
  | Tlet t1 (v, _, t2) => tys_of_term t1 ++ [vs_ty v] ++ tys_of_term t2
  | Tcase t ps => tys_of_term t ++ concat (map (fun x => tys_of_pat (fst (fst x)) ++ tys_of_term (snd x)) ps)
  | Teps (v, _, t) => vs_ty v :: tys_of_term t
  | Tquant _ (vs, _, _, t) => (map vs_ty vs) ++ tys_of_term t
  | Tbinop _ t1 t2 => tys_of_term t1 ++ tys_of_term t2
  | Tnot t => tys_of_term t
  | _ => nil
  end.

(*decl_node*)

(*Ignore projections*)
Definition tys_of_data_decl (d: data_decl) : list ty_c :=
  concat (map (fun c =>  tys_of_lsym (fst c)) (snd d)).

Definition tys_of_logic_decl (l: logic_decl) : list ty_c :=
  (tys_of_lsym (fst l)) ++ (tys_of_lsym (fst (fst (snd l)))) ++
  tys_of_term (snd (fst (snd l))).

Definition tys_of_ind_list (i: ind_list) : list ty_c :=
  concat (map (fun i => tys_of_lsym (fst i) ++ concat (map tys_of_term (map snd (snd i)))) (snd i)).

Definition tys_of_decl_node (d: decl_node) : list ty_c :=
  match d with
  | Dtype _ => nil
  | Ddata ls => concat (map tys_of_data_decl ls)
  | Dparam l => tys_of_lsym l
  | Dlogic ls => concat (map tys_of_logic_decl ls)
  | Dind i => tys_of_ind_list i
  | Dprop p => tys_of_term (snd p)
  end.


Definition tys_of_decl (d: decl) : list ty_c :=
  tys_of_decl_node (d_node d).

(*tdecl and task*)

Definition tys_of_tdecl_c (t: tdecl_c) : list ty_c :=
  match (td_node_of t) with
  | Decl d => tys_of_decl d
  | _ => nil
  end.

Fixpoint tys_of_task (t: task_hd) : list ty_c :=
  tys_of_tdecl_c (task_decl t) ++
    list_of_option tys_of_task (task_prev t).

(*2nd thing we need to get are decls. This is much simpler*)
Definition decls_of_tdecl_c (t: tdecl_c) : list decl :=
  match (td_node_of t) with
  | Decl d => [d]
  | _ => nil
  end.

Fixpoint decls_of_task (t: task_hd) : list decl :=
  decls_of_tdecl_c (task_decl t) ++
    list_of_option decls_of_task (task_prev t).

(*tdecls are similar (since we ignore Use and Clone)*)
Fixpoint tdecls_of_task (t: task_hd) : list tdecl_c :=
  task_decl t ::
    list_of_option tdecls_of_task (task_prev t).

(*And task_hd just flattens task into a list*)
Fixpoint task_hds_of_task (t: task_hd) : list task_hd :=
  t ::
  list_of_option task_hds_of_task (task_prev t).

(*And now the well-formed predicates*)

(*1. All types in the task are in the corresponding hash table and have 
  tags smaller than current counter*)

(*Do generically, all are the same*)
Definition all_in_hashtable {A} (hash: A -> Z) (eqb: A -> A -> bool) 
  (l: list A) (h:  CoqHashtbl.hashset A) : Prop :=
  forall x, In x l -> CoqHashtbl.find_opt_hashset hash eqb h x = Some x.

Definition all_idents_smaller {A} (hash: A -> Z) (l: list A) (i: Z) : Prop :=
  forall x, In x l -> (hash x < i)%Z.

Definition gen_hash_wf {A} (full_fn: full_st -> hashcons_ty A) (get: task_hd -> list A) 
  (hash: A -> Z) (eqb: A -> A -> bool) (t: task_hd) (st: full_st) : Prop :=
  all_in_hashtable hash eqb (get t) (hashcons_hash (full_fn st)) /\
  all_idents_smaller hash (get t) (hashcons_ctr (full_fn st)).

(*TODO: ensure these are the right hash functions, but should be*)

(*Types*)
Definition tys_hash_wf : task_hd -> full_st -> Prop := 
  gen_hash_wf full_ty_hash (fun t =>  concat (map tys_of_ty (tys_of_task t))) ty_hash ty_eqb.
(*Decls*)
Definition decls_hash_wf : task_hd -> full_st -> Prop :=
  gen_hash_wf full_decl_hash decls_of_task d_hash decl_eqb.
(*Tdecls*)
Definition tdecls_hash_wf : task_hd -> full_st -> Prop :=
  gen_hash_wf full_tdecl_hash tdecls_of_task td_hash tdecl_eqb.
(*Tasks*)
Definition task_hash_wf : task_hd -> full_st -> Prop :=
  gen_hash_wf full_task_hash task_hds_of_task task_hd_hash task_hd_eqb.

(*And the final predicate*)
Definition hashcons_wf (o: task) (s: full_st) : Prop :=
  match o with
  | Some t => tys_hash_wf t s /\ decls_hash_wf t s /\ tdecls_hash_wf t s /\ task_hash_wf t s
  | None => True
  end.
End HashCons.

(*The combined predicate*)
Definition st_wf (t: task) (s: full_st) : Prop :=
  idents_of_task_wf t s /\ hashcons_wf t s.

