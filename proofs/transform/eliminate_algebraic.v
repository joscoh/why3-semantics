Require Import amap.
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
(*This could be from a map or it could be e.g. the identity function*)
(*We only map to new names, we don't change the types (in real Why3, this is a clone)*)

Definition fpsym_clone (f: fpsym) (n: string) : fpsym :=
  Build_fpsym n (s_params f) (s_args f) (s_args_wf f) (s_params_nodup f).
(*If cloned, not constr*)
Definition funsym_clone (f: funsym) (n: string) : funsym :=
  Build_funsym (fpsym_clone f n) (f_ret f) false 0 (f_ret_wf f).

Variable (new_constr_name: funsym -> string).

(*Ignore no_sel and no_inv - not used anywhere*)
Variable (noind: typesym -> bool).

Section Badnames.
(*We need to make sure new funsym names are unique*)
Variable badnames: aset string.

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

(*NOTE: here we fix ty to [vty_cons ts (map vty_var (ts_args ts))] (i.e. adt_ty ts),
  or else we cannot prove the type variable inclusion*)
Lemma selector_check_args (ts: typesym) (csl: list funsym):
  let mt_var := gen_name "a" (list_to_aset (ts_args ts)) in
  let mt_ty : vty := vty_var mt_var in
  let ty := vty_cons ts (map vty_var (ts_args ts)) in
  let mt_al := ty :: rev_map (fun _ => mt_ty) csl in
(check_args (mt_var :: nodup string_dec (ts_args ts)) mt_al).
Proof.
  apply (reflect_iff _ _ (check_args_correct _ _)).
  intros x. simpl. intros [Hx | Hinx].
  - subst. simpl. rewrite list_to_aset_cons.
    eapply asubset_trans. 2: apply union_asubset_r.
    apply asubset_trans with (s2:=(list_to_aset (ts_args ts))).
    + rewrite asubset_def. intros x. simpl_set. setoid_rewrite in_map_iff.
      intros [y [[x1 [Hy Hinx1]] Hmemx]]; subst.
      simpl in Hmemx. simpl_set. subst. auto.
    + rewrite asubset_def. intros x. simpl_set. apply nodup_In.
  - unfold rev_map in Hinx. rewrite <- In_rev, in_map_iff in Hinx.
    destruct Hinx as [f [Hf Hinf]]; subst. simpl.
    rewrite list_to_aset_cons. apply union_asubset_l.
Qed. 

Lemma selector_args_nodup (ts: typesym):
  let mt_var := gen_name "a" (list_to_aset (ts_args ts)) in
  nodupb typevar_eq_dec (mt_var :: nodup string_dec (ts_args ts)).
Proof.
  simpl.
  apply (reflect_iff _ _ (nodup_NoDup _ _)).
  constructor.
  - rewrite nodup_In. intros Hx.
    apply gen_name_notin with (s:= (list_to_aset (ts_args ts)))(p:="a"%string).
    simpl_set; auto.
  - apply NoDup_nodup.
Qed.

Lemma selector_ret_sublist (ts: typesym)  :
  let mt_var := gen_name "a" (list_to_aset (ts_args ts)) in
  let mt_ty : vty := vty_var mt_var in
  check_asubset (type_vars mt_ty) (list_to_aset (mt_var :: nodup string_dec (ts_args ts))).
Proof.
  destruct (check_asubset _ _); simpl; auto. exfalso.
  apply n. simpl. rewrite list_to_aset_cons. apply union_asubset_l.
Qed.

Definition match_str : string := "match_".

Definition selector_name ts : string := (match_str ++ ts_name ts ++ under_str)%string.

(*The selector function symbol*)
Definition selector_funsym(ts: typesym) (csl: list funsym) : funsym :=
  let mt_id : string := gen_id (selector_name ts)  in
  let mt_var := gen_name "a" (list_to_aset (ts_args ts)) in
  let mt_ty : vty := vty_var mt_var in
  let ty := vty_cons ts (map vty_var (ts_args ts)) in
  (*Params: new name + all params in ts*)
  (*args are ty and then bunch of copies of mt_ty, 1 per constructor*)
  let mt_al := ty :: rev_map (fun _ => mt_ty) csl in
  Build_funsym (Build_fpsym mt_id (mt_var :: nodup string_dec (ts_args ts)) mt_al 
    (selector_check_args ts csl) (selector_args_nodup ts)) mt_ty false 0 (selector_ret_sublist ts).


(*The selector axiom for a given typesym and constructor list*)
Definition selector_axiom
  (ts: typesym) (csl: list funsym) : funsym * list (string * formula) :=
  (*fix ty*)
  let ty := vty_cons ts (map vty_var (ts_args ts)) in
  (* declare the selector function *)
  let mt_id : string := gen_id (selector_name ts) in
  (*NOTE, needs to be fresh, cannot be in params of ts*)
  let mt_var := gen_name "a" (list_to_aset (ts_args ts)) in
  let mt_ty : vty := vty_var mt_var in
  let mt_al := ty :: rev_map (fun _ => mt_ty) csl in
  let mt_ls := selector_funsym ts csl in
  (* define the selector function *)
  (*Generate new vars*)
  let varnames := gen_names (length csl) "z"%string aset_empty in
  let mt_vl : list vsymbol := rev_map (fun x => (x, mt_ty)) varnames in
  let mt_tl := rev_map Tvar mt_vl in
  let mt_add (cs: funsym) t :=
    let id := (mt_id ++ under_str ++ (s_name cs))%string in
    (*Create new vars - they can be the same among axioms*)
    let varnames2 := gen_names (length (s_args cs)) "u"%string (list_to_aset varnames) in
    let vl := rev (combine varnames2 (s_args cs)) in
    let newcs := new_constr cs in
    let hd := Tfun newcs (map vty_var (ts_args ts)) (rev_map Tvar vl)  in
    let hd := Tfun mt_ls (mt_ty :: (map vty_var (ts_args ts))) (hd :: mt_tl) in
    let vl := rev_append mt_vl (rev vl) in
    let ax := fforalls vl (Feq mt_ty hd t) in
    (id, ax)
  in 
  (mt_ls, map2 mt_add csl mt_tl).

Definition add_task_axioms (t: task) (axs: list (string * formula)) : task :=
  fold_left (fun acc x => add_axiom acc (fst x) (snd x)) axs t.


Definition add_selector_aux (tsk: task) (ts: typesym) (csl: list funsym) :=
  let sel := selector_axiom ts csl in
  let mt_ls := fst sel in
  let axms := snd sel in
  let tsk := add_param_decl tsk mt_ls in
  let tsk := add_task_axioms tsk axms in
  tsk.

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

(*Don't need selector for types with single constructor because trivial.*)

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
  destruct (check_asubset _ _); simpl; auto. exfalso; apply n.
  rewrite asubset_def.
  intros x Hinx. simpl_set_small. rewrite nodup_In. simpl_set. destruct Hinx as [y [Hiny Hinx]].
  rewrite in_map_iff in Hiny. destruct Hiny as [v [Hy Hinv]]; subst.
  simpl in Hinx. simpl_set. subst; auto.
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

Lemma check_asubset_empty {A: Type} `{countable.Countable A} (s: aset A):
  check_asubset aset_empty s.
Proof.
  destruct (check_asubset _ _); auto.
  exfalso. apply n. rewrite asubset_def. intros x Hinx.  simpl_set.
Qed.

Definition indexer_funsym (ts: typesym) : funsym :=
  let ty := vty_cons ts (map vty_var (ts_args ts))in
  let mt_id := gen_id (indexer_name ts) in
  Build_funsym (Build_fpsym mt_id (nodup typevar_eq_dec (ts_args ts)) [ty] 
    (indexer_check_args ts) (nodupb_nodup _ _)) vty_int false 0 (check_asubset_empty _).

(*Define indexer axiom*)
Definition indexer_axiom
  (ts: typesym) (csl : list funsym) : funsym * list (string * formula) :=
  (* declare the indexer function *)
  let mt_id := gen_id (indexer_name ts) in
  let mt_ls := indexer_funsym ts in 
  (* define the indexer function *)
  let mt_add idx (cs: funsym) :=
    let id := (mt_id ++ under_str ++ (s_name cs))%string in
    let varnames := gen_names (length (s_args cs)) "u" aset_empty in
    let vl := rev (combine varnames (s_args cs)) in
    let newcs := new_constr cs in
    let hd := Tfun newcs (map vty_var (ts_args ts)) (rev_map Tvar vl) in
    let ax := Feq vty_int (Tfun mt_ls (map vty_var (ts_args ts)) [hd])
      (Tconst (ConstInt (Z.of_nat idx))) in
    let ax := fforalls (rev vl) ax in
    (id, ax) in
  (mt_ls, mapi mt_add csl). 

Definition add_indexer_aux (tsk: task) (ts: typesym) (csl : list funsym) : task :=
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

Definition discriminator_axioms (ts: typesym) (ty: vty) (csl: list funsym) : 
  list (string * formula) :=
  let d_add (c1: funsym) (c2: funsym) : (string * formula) :=
    let i : string := gen_id ((s_name c1) ++ "_" ++ (s_name c2))%string in
    (*Create vars*)
    let ul := rev (combine (gen_names (length (s_args c1)) "u" aset_empty) (s_args c1)) in
    let vl := rev (combine (gen_names (length (s_args c2)) "v" aset_empty) (s_args c2)) in
    let newc1 := new_constr c1 in
    let newc2 := new_constr c2 in
    let t1 := Tfun newc1 (map vty_var (ts_args ts)) (rev_map Tvar ul) in
    let t2 := Tfun newc2 (map vty_var (ts_args ts)) (rev_map Tvar vl) in
    let ax := t_neq ty t1 t2 in
    let ax := fforalls (rev vl) ax in
    let ax := fforalls (rev ul) ax in
    (i, ax)
  in
  map_pairs d_add csl.


Definition add_discriminator (tsk: task) (ts: typesym) (ty: vty) (csl: list funsym) : task :=
  let axs := discriminator_axioms ts ty csl in
  add_task_axioms tsk axs.


(*Why3 adds the discriminator if more than 16 constructors, otherwise indexers. I guess
  too many axioms otherwise?*)
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

(*Projections are a bit trickier*)

(*Prove 3 obligations*)
Lemma check_args_ret (c: funsym):
  check_args (s_params c) [f_ret c].
Proof.
  simpl. rewrite andb_true_r.
  destruct c; simpl. auto.
Qed.

Lemma in_args_check_sublist (c: funsym) (ty: vty) (Hty: In ty (s_args c)):
  check_asubset (type_vars ty) (list_to_aset (s_params c)).
Proof.
  destruct c; simpl in *. 
  destruct f_sym; simpl in *.
  destruct (check_args_correct s_params s_args); [|discriminate].
  destruct (check_asubset (type_vars ty) _); simpl; auto.
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
  in
  dep_mapi _ conv_p (s_args c) (all_in_refl _).

Definition complete_projections (csl: list funsym) : list (funsym * list funsym) :=
  map (fun c => (c, projection_syms c)) csl.

(*Projection axioms*)

(*We consider projection axioms for a single constructor and list of projection symbols
  (given by [projection_names]) - pj_add from before*)
Definition projection_axioms
  (cs: funsym) (pl: list funsym) : list (funsym * (string * formula)) :=
  (* declare and define the projection functions *)
  let vl := combine (gen_names (length (s_args cs)) "u" aset_empty) (s_args cs) in
  let tl := map Tvar vl in
  let hd := Tfun (new_constr cs) (map vty_var (s_params cs)) tl in
  let add (tty: term * vty) (pj: funsym) :(funsym * (string * formula)) :=
    let t := fst tty in let ty := snd tty in
    let ls := pj in
    let id := ((s_name ls) ++ "'def")%string in
    let hh := Tfun ls (map vty_var (s_params cs)) [hd] in
    let ax := fforalls vl (Feq ty hh t) in
    (ls, (id, ax))
  in
  map2 add (combine tl (map snd vl)) pl.



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
  tsk.


Definition inversion_axiom
  (ts: typesym) (ty: vty) (csl: list funsym) : string * formula :=
  (* add the inversion axiom *)
  let ax_id := ((ts_name ts) ++ "_inversion")%string in
  let ax_vs := (gen_name "u"%string aset_empty, ty) in 
  let ax_hd := Tvar ax_vs in
  let mk_cs (cs: funsym) : formula :=
    (*NOTE: we know the pjl from the projections*)
    let pjl := projection_syms cs in
    let app pj := Tfun pj (map vty_var (ts_args ts)) [ax_hd] in
    let cs := new_constr cs in
    let pjl' := map app pjl in
    Feq ty ax_hd (Tfun cs (map vty_var (ts_args ts)) pjl')
  in
  let ax_f := map_join_left' Ftrue mk_cs (Fbinop Tor) csl in
  let ax_f := Fquant Tforall ax_vs ax_f (*t_forall_close [ax_vs] [] ax_f in*) in
  (ax_id, ax_f).


Definition add_inversion (tsk: task) (ts: typesym) (ty: vty) (csl: list funsym) :
  task :=
  let inv := inversion_axiom ts ty csl in
  add_axiom tsk (fst inv) (snd inv).


Definition add_param_decls (l: list funsym) (tsk: task) : task :=
  fold_left add_param_decl l tsk.

Definition adt_ty (ts: typesym) : vty := vty_cons ts (map vty_var (ts_args ts)).

(*Add all axioms*)
Definition add_axioms (tsk: task) (d: typesym * list funsym) : task :=
  let ts := fst d in
  let csl := snd d in
  let ty := adt_ty ts in
  let tsk := add_param_decls (map new_constr csl) tsk in
  (* add selector, projections, and inversion axiom *)
  let tsk := add_selector tsk ts csl in
  let tsk := add_indexer tsk ts ty csl in
  let tsk := add_projections tsk ts ty csl in
  add_inversion tsk ts ty csl.

(*Skip [add_tags] and finding infinite types - only deals with metas*)

(*rewriting*)

Section Rew.
Variable (gamma: context). (*to look up constructors*)

(*We can define the function giving [mt_map]*)
Definition get_mt_map (t: typesym) : funsym :=
  match (find_ts_in_ctx gamma t) with
  | Some (m, a) => fst (selector_axiom t (adt_constr_list a))
  | _ => id_fs
  end.

(*NOTE: bad, can we find the type differently?*)
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


(*Assume we have a list of banned variables (later instantiate with term vars)*)
Variable badvars : aset vsymbol.

(*NOTE: changed to [fold_right], so not rev anymore*)
Definition get_proj_list (c: funsym) : list funsym := (projection_syms c).

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
      let pjl := get_proj_list cs  in 
      let e := fold_let Tlet (map2 add_var pl pjl) e in
      (w, amap_set m cs e)
  | Pwild => (Some e, m)
  | _ => (*Prove don't hit*) x
  end.

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
        | _ => (* prove don't hit*) vs_d
      end in
      (w, amap_set m cs (map get_var pl, e))
    | Pwild => (Some e, m)
    | _ => (*prove dont hit*) x
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

(*legacy, can inline now*)
Definition rewriteF_default_case ty1 t1 (sign: bool) vl hd e : formula :=
  let hd := Feq ty1 t1 hd in if sign then fforalls vl (Fbinop Timplies hd e)
    else fexists vl (Fbinop Tand hd e).

(*Also separate out [find]*)
(*big difference from Why3 - removed let case - 
    not any faster (on Why3 test suite) and MUCH harder to prove correct*)
Definition rewriteF_find (t1: term) (ty1: vty) (args: list vty) (sign: bool)
  (m: amap funsym (list vsymbol * formula))
  (w: option formula) (cs: funsym) : 
  formula :=
  let res := match amap_lookup m cs with
  | Some y => y
  | None => 
      let names := gen_strs (length (s_args cs)) badvars in
      let tys := ty_subst_list (s_params cs) args (s_args cs) in
      let vars := combine names tys : list vsymbol in
      (vars, match w with | Some y => y | None => Ftrue end)
  end
  in
  let vl := fst res in let e := snd res in
  let hd := Tfun (new_constr cs) args (map Tvar vl) in
  rewriteF_default_case ty1 t1 sign vl hd e .


(*Eliminating pattern matches*)
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
        match amap_lookup m x with
        | Some e => e
        | None => match w with | Some x => x | None => (*impossible*) tm_d end
        end
      in
     
      let tl := map find (get_constructors gamma ts) in
      match (get_single tl) with 
      | Left x => proj1_sig x
      | Right _ =>
        Tfun (get_mt_map ts) (pat_match_ty' pats :: args) (t1 :: tl)
      end
    else t_map rewriteT (rewriteF true) t
  | Tfun ls tys args => (*map old constrs to new constr*)
    if ls.(f_is_constr) && enc_ty (f_ret ls) (*we can just pass in return type because only depends on typesym*)
    then Tfun (new_constr ls) tys 
      (map rewriteT args)
    else t_map rewriteT (rewriteF true) t
  | _ => t_map rewriteT (rewriteF true) t
  end
with rewriteF (sign: bool) (f: formula) : formula := 
  match f with
  | Fmatch t1 ty1 pats =>
    if enc_ty ty1 then
      let t1 := rewriteT t1 in
      let res := mk_brs_fmla (rewriteF sign) pats in
      let w := fst res in
      let m := snd res in
      (*By typing, has to be an ADT*)
      let ts := match ty1 with | vty_cons ts _ => ts | _ => ts_d (*impossible*) end in
      let args := match ty1 with | vty_cons _ args => args | _ => nil (*impossible*) end in
      let op := if sign then (Fbinop Tand) else (Fbinop Tor) in
      map_join_left' Ftrue (rewriteF_find t1 ty1 args sign m w) op (get_constructors gamma ts)
    else f_map_sign (fun _ => rewriteT) rewriteF sign f
  | Fquant q v f1 =>
    if (quant_eqb q Tforall && sign) || (quant_eqb q Texists && negb sign) then
      Fquant q v (rewriteF sign f1)
    else f_map_sign (fun _ => rewriteT) rewriteF sign f
  | Fbinop o _ _ =>
    if (binop_eqb o Tand && sign) || (binop_eqb o Tor && negb sign) then
      f_map_sign (fun _ => rewriteT) rewriteF sign f (*not nil*)
    else f_map_sign (fun _ => rewriteT) rewriteF sign f
  | Flet t1 _ _ =>
    f_map_sign (fun _ => rewriteT) rewriteF sign f 
  | _ => f_map_sign (fun _ => rewriteT) rewriteF sign f
  end.

End Rew.

(*Instantiate badvars with term variables*)

Definition rewriteT' gamma t :=
  rewriteT gamma (aset_union (tm_fv t) (list_to_aset (tm_bnd t))) t.
Definition rewriteF' gamma x f :=
  rewriteF gamma (aset_union (fmla_fv f) (list_to_aset (fmla_bnd f))) x f.

(*Put everything together*)

Definition add_ty_decl (t: task) (ts: typesym) : task :=
  (abs_type ts :: task_gamma t, task_delta t, task_goal t).

Definition add_def (d: def) (t: task) : task :=
  (d :: task_gamma t, task_delta t, task_goal t).

(*Add mut with params from given mut and list of ADTs (should be subset)*)
Definition add_mut (m: mut_adt)(tys: list alg_datatype) (t: task) : task :=
  add_def (datatype_def (mk_mut tys (m_params m) (m_nodup m))) t.

(*NOTE: adding context here because we want to generalize context for [rewriteT']*)
Definition comp_ctx (gamma: context) (d: def) (tsk: task) : task :=
  match d with
  | datatype_def m =>
    let dl := typs m in
    (*NOTE: made it fold_right to keep same order as context - should change in real version too
      Also, we are limited to keeping/axiomatizing entire mut - so all concrete or all abstract*)
    let tsk := if (keep_muts m) then add_def d tsk else 
      List.fold_right (fun a t => add_ty_decl t (adt_name a)) tsk dl
    in
    (* add needed functions and axioms *)
    let st := List.fold_left add_axioms (map (fun a => (adt_name a, adt_constr_list a)) dl) tsk in
    st
  | _ => 
    (*rewriting case*)
    add_def (TaskGen.def_map (rewriteT' gamma) (rewriteF' gamma true) d) tsk
  end.

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
    let badnames := list_to_aset (idents_of_context (task_gamma t)) in
    let tsk1 := fold_all_ctx badnames t in
    (*NOTE: HAS to be (task_gamma t) here when we do this way - or else
      nothing has constructors for rewriteT  --
      this is because we are folding whole context at once instead of
      doing each definition and then task (NOTE: this is a substantive difference
      from theirs!))*)
    let del1 := map (rewriteF' badnames (task_gamma t) true) (map snd (task_delta tsk1)) in
    let g1 := rewriteF' badnames (task_gamma t) true (task_goal tsk1) in
    [(task_gamma tsk1, (combine (map fst (task_delta tsk1)) del1), g1)]. 

Section FullTrans.

Definition eliminate_match : trans :=
  compose_trans compile_match fold_comp.

(*Note that eliminate_match is the same - with extra meta stuff we don't care about*)

Definition eliminate_algebraic : trans :=
  compose_trans compile_match fold_comp.

End FullTrans.

End ElimADT.

