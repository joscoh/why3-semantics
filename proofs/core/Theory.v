Require Export FullInterp.
(*Why3 Theories*)


(*We depart from Why3 notation slightly here, since we make a distinction
  between a context (with declarations) and a theory
  environment, which contains lemmas, axioms, goals, and 
  use/clone of another theory*)

(*Syntax*)
(*From why3/core/decl.ml*)
  Inductive prop_kind : Set :=
  | Plemma    (* prove, use as a premise *)
  | Paxiom    (* do not prove, use as a premise *)
  | Pgoal.     (* prove, do not use as a premise *)


  (*
Unset Elimination Schemes.
Inductive tdecl : Set :=
  | tdef : def -> tdecl 
  | tprop : prop_kind -> string -> formula -> tdecl
  | tuse : theory -> bool -> tdecl
  | tclone : theory -> string -> list (typesym * typesym) ->
  list (funsym * funsym) -> list (predsym * predsym) -> bool -> tdecl
with theory : Set :=
  | ttheory : list tdecl -> theory.
Scheme tdecl_ind := Induction for tdecl Sort Prop
with theory_ind := Induction for theory Sort Prop.
Scheme tdecl_rec := Induction for tdecl Sort Type
with theory_rec := Induction for theory Sort Type.
Check tdecl_rec.*)
(*ALT (maybe better) - use old, use Equations with size measure
better - define size of tdecl, lift to list, use as measure*)

(*We require 2 additional restrictions that why3 does not have
  (at least for now)
  1. All "clone"d theories must be exported
  2. All "clone"d theories must use qualified names
  
  With these restrictions, we can define notions of well-typed
  and valid theories and we can check these efficiently.
  In particular, we can identify all of the theories "use"d in
  a theory T and require that if we use/clone T in A, as long
  as we use all the same theories that T depends on, the
  resulting theory A is well-typed/proved.
  This means that we do not need to re-check things that
  we have already typed/verified, which is crucial for 
  performance and modularity
  *)

(*We can view theories as comprising 2 things:
  A context (formed by the definitions as well as the uses
    and clones of other theories)
  and a set of goals/lemmas/axioms
  There is some work to be done in getting the context;
  we need to substitute with the given maps for cloning
  and we need to ensure that we do not duplicate theories
  and result in a non-well-formed context.
  
  To do this, we separate the context formed from
  a given theory into the internal context (what we need
    to prove things, expanding all "use" and "clone")
  and the external one, which only includes "use"s
  marked as exported (all "clone"s are exported in our
  system)
  *)

(*Substitution*)

Section Sub.

Variable (tys: list (typesym * typesym))
(funs: list (funsym * funsym)) (preds: list (predsym * predsym)).

Definition sub_from_map {A: Set} (eq_dec: forall (x y: A), {x=y} +{x<>y})
  (m: list (A * A)) (x: A) :=
  match (get_assoc_list eq_dec m x) with
  | Some y => y
  | None => x
  end.

Definition sub_tys := sub_from_map typesym_eq_dec tys.
Definition sub_funs := sub_from_map funsym_eq_dec funs.
Definition sub_preds := sub_from_map predsym_eq_dec preds.

(*Sub in vty - only typesyms substituted*)
Fixpoint sub_in_vty (t: vty) :=
  match t with
  | vty_int => vty_int
  | vty_real => vty_real
  | vty_var x => vty_var x
  | vty_cons ts vs =>
    vty_cons (sub_tys ts) (map sub_in_vty vs)
  end.

Lemma sub_in_vty_vars t:
  type_vars (sub_in_vty t) = type_vars t.
Proof.
  induction t; simpl; auto.
  induction vs; simpl; auto.
  inversion H; subst.
  rewrite H2. f_equal. auto.
Qed.

Lemma check_args_sub {params args}:
  check_args params args ->
  check_args params (map sub_in_vty args).
Proof.
  unfold is_true.
  rewrite <- !(reflect_iff _ _ (check_args_correct _ _)); intros.
  unfold sublist in *.
  intros.
  rewrite in_map_iff in H0.
  destruct H0 as [t [Ht Hint]]; subst.
  rewrite sub_in_vty_vars in H1.
  apply (H _ Hint); auto.
Qed.

Lemma check_sublist_sub {t params}:
  check_sublist (type_vars t) params ->
  check_sublist (type_vars (sub_in_vty t)) params.
Proof.
  rewrite sub_in_vty_vars; auto.
Qed.

(*Sub in fpsym*)
Definition sub_in_fpsym (f: fpsym) : fpsym :=
  Build_fpsym (s_name f) (s_params f)
    (map sub_in_vty (s_args f))
    (check_args_sub (s_args_wf f))
    (s_params_nodup f).

(*Sub in funsym - only typesyms substituted*)
Definition sub_in_funsym (f: funsym) : funsym :=
  Build_funsym (sub_in_fpsym f)
  (sub_in_vty (f_ret f))
  (check_sublist_sub (f_ret_wf f)).

(*Sub in alg_datatype - only typesyms can be substituted*)

(*TODO: move*)
Fixpoint map_ne_list {A B: Set} (f: A -> B) (l: ne_list A) : ne_list B :=
  match l with
  | ne_hd x => ne_hd (f x)
  | ne_cons x tl => ne_cons (f x) (map_ne_list f tl)
  end.

Lemma map_ne_list_spec {A B: Set} (f: A -> B) (l: ne_list A):
  ne_list_to_list (map_ne_list f l) = map f (ne_list_to_list l).
Proof.
  induction l; simpl; auto.
  rewrite IHl; auto.
Qed.

Definition sub_in_adt (a: alg_datatype) : alg_datatype :=
  match a with
  | alg_def ts fs => alg_def ts (map_ne_list sub_in_funsym fs)
  end.

(*Sub in mut*)
Definition sub_in_mut (m: mut_adt) : mut_adt :=
  mk_mut (map sub_in_adt (typs m)) (m_params m) (m_nodup m).

(*Substitute in term - now we can substitute all 3*)

Definition sub_in_vs (x: vsymbol) : vsymbol :=
  (fst x, sub_in_vty (snd x)).

(*Can only sub typesyms here - can't sub in constrs*)
Fixpoint sub_in_p (p: pattern) : pattern :=
  match p with
  | Pvar x => Pvar (sub_in_vs x)
  | Pwild => Pwild
  | Por p1 p2 => Por (sub_in_p p1) (sub_in_p p2)
  | Pbind p x => Pbind (sub_in_p p) (sub_in_vs x)
  | Pconstr f tys ps => Pconstr f (map sub_in_vty tys) (map sub_in_p ps)
  end.

Fixpoint sub_in_t (t: term) : term :=
  match t with
  | Tconst c => Tconst c
  | Tvar v => Tvar (sub_in_vs v)
  | Tfun fs tys tms =>
    Tfun (sub_funs fs) (map sub_in_vty tys)
      (map sub_in_t tms)
  | Tlet t1 v t2 =>
    Tlet (sub_in_t t1) (sub_in_vs v) (sub_in_t t2)
  | Tif f t1 t2 =>
    Tif (sub_in_f f) (sub_in_t t1) (sub_in_t t2)
  | Tmatch t ty ps =>
    Tmatch (sub_in_t t) (sub_in_vty ty)
      (map (fun x => (sub_in_p (fst x), sub_in_t (snd x))) ps)
  | Teps f x => Teps (sub_in_f f) (sub_in_vs x)
  end
with sub_in_f (f: formula) : formula :=
  match f with
  | Fpred p tys tms => Fpred (sub_preds p) (map sub_in_vty tys)
    (map sub_in_t tms)
  | Fquant q x f => Fquant q (sub_in_vs x) (sub_in_f f)
  | Feq ty t1 t2 => Feq (sub_in_vty ty) (sub_in_t t1) (sub_in_t t2)
  | Fbinop b f1 f2 => Fbinop b (sub_in_f f1) (sub_in_f f2)
  | Fnot f => Fnot (sub_in_f f)
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  | Flet t v f => Flet (sub_in_t t) (sub_in_vs v) (sub_in_f f)
  | Fif f1 f2 f3 => Fif (sub_in_f f1) (sub_in_f f2) (sub_in_f f3)
  | Fmatch t ty ps =>
    Fmatch (sub_in_t t) (sub_in_vty ty)
    (map (fun x => (sub_in_p (fst x), sub_in_f (snd x))) ps)
  end.

(*Substitute in funpred_def*)
Definition sub_in_funpred_def (x: funpred_def) : funpred_def :=
  match x with
  (*Cannot sub funsym in definition*)
  | fun_def f xs t => fun_def f (map sub_in_vs xs) (sub_in_t t)
  | pred_def p xs f => pred_def p (map sub_in_vs xs) (sub_in_f f)
  end.

(*Substitue in [indpred_def]*)
Definition sub_in_indpred_def (x: indpred_def) : indpred_def :=
  match x with
  (*Cannot change indpred predsym*)
  | ind_def p xs => ind_def p (map (fun x => (fst x, sub_in_f (snd x))) xs)
  end.

(*Substitute according to map in context*)

Definition sub_ctx_map (c: context)  :
  context :=
  fold_right (fun x (acc: list def) =>
    match x with
    (*Abstract: remove iff instantiate*)
    | abs_type ts => if in_dec typesym_eq_dec ts (map fst tys) then acc
      else x :: acc
    | abs_fun f => if in_dec funsym_eq_dec f (map fst funs) then acc
      else x :: acc
    | abs_pred p => if in_dec predsym_eq_dec p (map fst preds) then acc
      else x :: acc
    (*Concrete - need to substitute*)
    | datatype_def m =>  
      datatype_def (sub_in_mut m) :: acc
    | recursive_def l =>
      recursive_def (map sub_in_funpred_def l) :: acc
    | inductive_def l =>
      inductive_def (map sub_in_indpred_def l) :: acc
    end
  ) nil c.

(*Substitute according to map in list of (string * formula)*)
Definition sub_props_map (l: list (string * formula)) : list (string * formula) :=
  map (fun x => (fst x, (sub_in_f (snd x)))) l.

End Sub.

(*From why3 theory.ml - they use string -> typesym, etc maps
  I should too, eventually*)
Record namespace := mk_ns {
  ns_ts: list (string * typesym);
  ns_fs: list (string * funsym);
  ns_ps: list (string * predsym)
}.

Definition ts_in_ns (t: typesym) (n: namespace) : bool :=
  match (get_assoc_list string_dec (ns_ts n) (ts_name t) ) with
  | Some t1 => typesym_eq_dec t t1
  | None => false
  end.

Definition fs_in_ns (f: funsym) (n: namespace) : bool :=
  match (get_assoc_list string_dec (ns_fs n) (s_name f) ) with
  | Some f1 => funsym_eq_dec f f1
  | None => false
  end.

Definition ps_in_ns (p: predsym) (n: namespace) : bool :=
  match (get_assoc_list string_dec (ns_ps n) (s_name p) ) with
  | Some p1 => predsym_eq_dec p p1
  | None => false
  end.

(*Qualified names*)
Section QualNames.

(*Change all top-level type, function, and predicate
  definitions to use a qualified prefix*)
Variable prefix : string.

Variable n: namespace.
Local Open Scope string_scope.
Definition add_prefix (s: string) := prefix ++ "."%string ++ s.

Definition qual_ts (t: typesym) : typesym :=
  mk_ts (add_prefix (ts_name t)) (ts_args t).

Definition qual_ts_n (t: typesym) : typesym :=
  if ts_in_ns t n then qual_ts t else t.

Fixpoint qual_vty (v: vty) : vty :=
  match v with
  | vty_int => vty_int
  | vty_real => vty_real
  | vty_var x => vty_var x
  | vty_cons ts vs => vty_cons (qual_ts_n ts) (map qual_vty vs)
  end.

Lemma qual_vty_vars t:
  type_vars (qual_vty t) = type_vars t.
Proof.
  induction t; simpl; auto.
  induction vs; simpl; auto.
  inversion H; subst.
  rewrite H2. f_equal. auto.
Qed.

Lemma check_args_qual {params args}:
  check_args params args ->
  check_args params (map qual_vty args).
Proof.
  unfold is_true.
  rewrite <- !(reflect_iff _ _ (check_args_correct _ _)); intros.
  unfold sublist in *.
  intros.
  rewrite in_map_iff in H0.
  destruct H0 as [t [Ht Hint]]; subst.
  rewrite qual_vty_vars in H1.
  apply (H _ Hint); auto.
Qed.

Lemma check_sublist_qual {t params}:
  check_sublist (type_vars t) params ->
  check_sublist (type_vars (qual_vty t)) params.
Proof.
  rewrite qual_vty_vars; auto.
Qed.

Definition qual_fpsym (f: fpsym) : fpsym :=
  Build_fpsym (add_prefix (s_name f)) (s_params f)
    (map qual_vty (s_args f)) (check_args_qual (s_args_wf f)) 
    (s_params_nodup f).

Definition qual_funsym (f: funsym) : funsym :=
  Build_funsym (qual_fpsym (f_sym f))
    (qual_vty (f_ret f))
    (check_sublist_qual (f_ret_wf f)).

Definition qual_funsym_n (f: funsym) : funsym :=
  if fs_in_ns f n then qual_funsym f else f.

Definition qual_predsym (p: predsym) : predsym :=
  Build_predsym (qual_fpsym p).

Definition qual_predsym_n (p: predsym) : predsym :=
  if ps_in_ns p n then qual_predsym p else p.

Definition qual_alg_datatype (a: alg_datatype) : alg_datatype :=
  match a with
  | alg_def ts fs => alg_def (qual_ts ts) (map_ne_list qual_funsym_n fs)
  end.

Definition qual_mut_adt (m: mut_adt) : mut_adt :=
  mk_mut (map qual_alg_datatype (typs m)) (m_params m)
  (m_nodup m).

Definition qual_vs (x: vsymbol) : vsymbol :=
  (fst x, qual_vty (snd x)).

Fixpoint qual_pat (p: pattern) : pattern :=
  match p with
  | Pvar v => Pvar (qual_vs v)
  | Pconstr fs tys pats => Pconstr (qual_funsym_n fs) (map qual_vty tys)
    (map qual_pat pats)
  | Pwild => Pwild
  | Por p1 p2 => Por (qual_pat p1) (qual_pat p2)
  | Pbind p x => Pbind (qual_pat p) (qual_vs x)
  end.
  
Fixpoint qual_tm (t: term) : term :=
  match t with
  | Tconst c => Tconst c
  | Tvar v => Tvar (qual_vs v)
  | Tfun fs tys tms => Tfun (qual_funsym_n fs) (map qual_vty tys) 
    (map qual_tm tms)
  | Tlet t1 v t2 => Tlet (qual_tm t1) (qual_vs v) (qual_tm t2)
  | Tif f t1 t2 => Tif (qual_fmla f) (qual_tm t1) (qual_tm t2)
  | Tmatch t v ps => Tmatch (qual_tm t) (qual_vty v)
    (map (fun x => (qual_pat (fst x), qual_tm (snd x))) ps)
  | Teps f v => Teps (qual_fmla f) (qual_vs v)
  end
with qual_fmla (f: formula) : formula :=
  match f with
  | Fpred p tys tms => Fpred (qual_predsym_n p) (map qual_vty tys)
    (map qual_tm tms)
  | Fquant q v f => Fquant q (qual_vs v) (qual_fmla f)
  | Feq ty t1 t2 => Feq (qual_vty ty) (qual_tm t1) (qual_tm t2)
  | Fbinop b f1 f2 => Fbinop b (qual_fmla f1) (qual_fmla f2)
  | Fnot f => Fnot (qual_fmla f)
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  | Flet t v f => Flet (qual_tm t) (qual_vs v) (qual_fmla f)
  | Fif f1 f2 f3 => Fif (qual_fmla f1) (qual_fmla f2) (qual_fmla f3)
  | Fmatch t v ps => Fmatch (qual_tm t) (qual_vty v)
    (map (fun x => (qual_pat (fst x), qual_fmla (snd x))) ps)
  end.

Definition qual_funpred_def (f: funpred_def) : funpred_def :=
  match f with
  | fun_def f xs t => fun_def (qual_funsym_n f) (map qual_vs xs) (qual_tm t)
  | pred_def p xs f => pred_def (qual_predsym_n p) (map qual_vs xs)
    (qual_fmla f)
  end.

Definition qual_indpred_def (i: indpred_def) : indpred_def :=
  match i with
  | ind_def p xs => ind_def (qual_predsym_n p) 
    (map (fun x => (add_prefix (fst x), qual_fmla (snd x))) xs)
  end.

Definition qual_def (d: def) : def :=
  match d with
  | datatype_def m => datatype_def (qual_mut_adt m)
  | recursive_def l => recursive_def (map qual_funpred_def l)
  | inductive_def i => inductive_def (map qual_indpred_def i)
  | abs_type ts => abs_type (qual_ts_n ts)
  | abs_fun f => abs_fun (qual_funsym_n f)
  | abs_pred p => abs_pred (qual_predsym_n p)
  end.

End QualNames.


(*Get all definitions from a theory*)

(*Problem - to get definition, need to have qualified names*)


(*Here's what I will do:
  theory will be mutually recursive with tdecl
  theory consists of list tdecl, list typesym, list funsym,
    list predsym
  these lists represent the (external) namespace of the the
  theory

  then, qualify a theory as follows:
  identify all of the "uses" in the theory and look at 
  all of their lists
  qualify everything in the theory EXCEPT for the things
  in this list
  (and update the external lists appropriately)
  alternatively, update lists first, qualify everything IN list

  then, to get context of theory, qualify "clones" using this

  this solves the problem of circular dependencies

  problem before: qualify theory -> need names to
    (not) qualify, look through "use", need to qualify
    inner theories - here, dont have functions, store data,
    assume populated correctly and we will ensure that this
    is the case

*)


(*We take a somewhat lazy approach to implementing theories:
  we see theories as simply some preprocessing that produces
  a context and a series of goals. We then typecheck the
  context and prove the goals separately.
  This means that we have no checks within the theory 
  (for example, for duplicates), relying on the later
  typechecking.

  There are more efficient ways to do this to avoid 
  re-typechecking things we have already done, but 
  we do not implement that for the moment.
*)

(*
Unset Elimination Schemes.
*)
Inductive tdecl : Set :=
  | tdef : def -> tdecl
  | tprop : prop_kind -> string -> formula -> tdecl
  (*Use a theory (copy all of its definitions).
    Bool represents if exported or not*)
  | tuse : list tdecl -> bool -> tdecl
  (*Clone a theory - instantiating some parameters and giving
    a qualified name*)
  | tclone: list tdecl -> option string -> list (typesym * typesym) ->
    list (funsym * funsym) -> list (predsym * predsym) -> tdecl.

Definition theory := list tdecl.
(*
with theory : Set :=
  | mk_theory : list tdecl -> namespace -> theory.

Scheme tdecl_ind := Induction for tdecl Sort Prop
  with theory_ind := Induction for theory Sort Prop.
Scheme tdecl_rec := Induction for tdecl Sort Type
  with theory_rec := Induction for theory Sort Type.
Set Elimination Schemes.*)

(*Qualify names in a theory*)

(*Definition th_export (t: theory) : namespace :=
  match t with
  | mk_theory _ n => n
  end.*)


(*To write inductive functions over theories that
  recurse as we expect (into tuse and tclone), we define a 
  notion of "size"*)
  Fixpoint tdecl_size (t: tdecl) : nat :=
    match t with
    | tdef d => 1
    | tprop _ _ _ => 1
    | tuse ts _ => 1 + sum (map tdecl_size ts)
    | tclone ts _ _ _ _ => 1 + sum (map tdecl_size ts)
    end.
  
  Definition theory_size (t: theory) : nat :=
    sum (map tdecl_size t).
  
  
  
  (*We use Equations because we write functions that are
    not obviously stucturally
    recursive (or at least Coq cannot tell that they are)*)
  
  (* #[local] Instance theory_size_wf:
  Classes.WellFounded
          (Telescopes.tele_measure (Telescopes.tip theory) nat
             (fun t : theory => theory_size t) lt).
  unfold Classes.WellFounded, Telescopes.tele_measure. simpl.
  apply Inverse_Image.wf_inverse_image.
  apply Nat.lt_wf_0.
  Defined.*)
  
  From Equations Require Import Equations.
  (*Solves all goals*)
  Obligation Tactic := intros; try (unfold theory_size); simpl; try lia.
  
  (*We need a bunch of utilities*)
(*Utilities for namespace (move)*)
Definition emp_namespace : namespace :=
  mk_ns nil nil nil.

Definition add_ts_to_ns (tss: list typesym) (n: namespace) : namespace :=
  mk_ns (map (fun x => (ts_name x, x)) tss ++ (ns_ts n)) (ns_fs n) (ns_ps n).

Definition add_fs_to_ns (fss: list funsym) (n: namespace) : namespace :=
  mk_ns (ns_ts n) (map (fun (x: funsym) => (s_name x, x)) fss ++ (ns_fs n))
    (ns_ps n).

Definition add_ps_to_ns (pss: list predsym) (n: namespace) : namespace :=
  mk_ns (ns_ts n) (ns_fs n) 
  (map (fun (x: predsym) => (s_name x, x)) pss ++ (ns_ps n)).

Definition add_def_to_ns (d: def) (n: namespace) : namespace :=
  add_ps_to_ns (predsyms_of_def d) 
    (add_fs_to_ns (funsyms_of_def d)
      (add_ts_to_ns (typesyms_of_def d) n)).

(*TODO: should really be union*)
Definition merge_ns (n1 n2: namespace) : namespace :=
  mk_ns ((ns_ts n1) ++ (ns_ts n2)) ((ns_fs n1) ++ (ns_fs n2))
    ((ns_ps n1) ++ (ns_ps n2)).

(*Add s as prefix to all entries in namespace*)
Definition qualify_all (s: string) (n: namespace) : namespace :=
  mk_ns (map (fun x => (add_prefix s (fst x), qual_ts_n s n (snd x))) (ns_ts n))
    (map (fun x => (add_prefix s (fst x), qual_funsym_n s n (snd x))) (ns_fs n))
    (map (fun x => (add_prefix s (fst x), qual_predsym_n s n (snd x))) (ns_ps n)).



(*Get all exported names (only) from a theory*)
Equations get_exported_names (t: theory) : namespace 
  by wf (theory_size t) lt :=
get_exported_names nil := emp_namespace;
get_exported_names (tdef d :: tl) := 
  add_def_to_ns d (get_exported_names tl);
get_exported_names (tprop _ _ _ :: tl) := get_exported_names tl;
get_exported_names (tuse th true :: tl) := 
  merge_ns (get_exported_names th) (get_exported_names tl);
get_exported_names (tuse th false :: tl) := get_exported_names tl;
get_exported_names (tclone th (Some s) tys funs preds :: tl) :=
  merge_ns (qualify_all s (get_exported_names th)) (get_exported_names tl);
(*If None, do not qualify*)
get_exported_names (tclone th None tys funs preds :: tl) :=
  merge_ns (get_exported_names th) (get_exported_names tl)
.

Definition add_qual (s1 s2: string) :=
  (s1 ++ "."%string ++ s2)%string.


(*Now we can qualify a theory - replace all exported definitions
  and uses of these definitions (BUT NOT used-but-not-exported defs)
  with qualified symbols*)
Equations qualify_theory (s: string) (n: namespace) (t: theory) : theory 
  by wf (theory_size t) lt :=
qualify_theory s n nil := nil;
qualify_theory s n (tdef d :: tl) := 
  tdef (qual_def s n d) :: qualify_theory s n tl;
qualify_theory s n (tprop k name f :: tl) :=
  (tprop k (add_prefix s name) (qual_fmla s n f)) :: qualify_theory s n tl;
(*A used theory that is exported is qualified - we add all qualified
  defs to our theory*)
qualify_theory s n (tuse th true :: tl) :=
  tuse (qualify_theory s n th) true :: qualify_theory s n tl;
(*If not used, don't add*)
qualify_theory s n (tuse th false :: tl) := qualify_theory s n tl;
(*Cloned theories are qualified first, then qualified again (see)*)
qualify_theory s n (tclone th (Some name) tys funs preds :: tl) :=
  tclone (qualify_theory (add_qual s name) n th) (Some name) (*TODO: qualify name?*)
    tys funs preds :: qualify_theory s n tl;
qualify_theory s n (tclone th None tys funs preds :: tl) :=
  tclone (qualify_theory s n th) None 
    tys funs preds :: qualify_theory s n tl
  .

Set Bullet Behavior "Strict Subproofs".

(*Qualified theory has same size*)
Lemma qualify_theory_size (s: string) (n: namespace) (t: theory) :
  theory_size (qualify_theory s n t) <= theory_size t.
Proof.
  revert s n t.
  apply (qualify_theory_elim (fun s n t1 t2 => theory_size t2 <= theory_size t1));
  simpl; intros; auto; unfold theory_size in *; simpl; lia.
Qed.

(*Now, we can get the internal and external context of a theory.
  We also give the exported axioms and lemmas*)

Equations theory_ctx_ext (t: theory) : context
  by wf (theory_size t) lt :=
theory_ctx_ext (tdef d :: tl) := d :: theory_ctx_ext tl;
theory_ctx_ext (tuse l true :: tl) :=
  (*Not structurally recursive*)
  theory_ctx_ext l ++ theory_ctx_ext tl;
theory_ctx_ext (tclone l o tys funs preds :: tl) :=
  (*for a clone, we first get the exported names to qualify, then
    we qualify, then we sub in (so the sub takes the qualified names)*)
  let n := get_exported_names l in
  let qual := 
  match o with | Some name => qualify_theory name n l | None => l end in 
  sub_ctx_map tys funs preds (theory_ctx_ext qual) ++ theory_ctx_ext tl;
theory_ctx_ext (_ :: tl) := theory_ctx_ext tl;
theory_ctx_ext nil := nil.
Next Obligation.
subst qual. destruct o; simpl; try lia.
pose proof (qualify_theory_size s n l). 
unfold theory_size in *. lia.
Defined.

(*And the internal theory context - only use external context
  of imported modules - this one is structurally recursive*)
Fixpoint theory_ctx_int (t: theory) : context :=
  match t with
  | tdef d :: tl => d :: theory_ctx_int tl
  | tuse l _ :: tl =>
      theory_ctx_ext l ++ theory_ctx_int tl
  | tclone l o tys funs preds  :: tl =>
    let n := get_exported_names l in
    let qual := 
      match o with | Some name => qualify_theory name n l | None => l end in
    sub_ctx_map tys funs preds (theory_ctx_ext qual) ++ theory_ctx_int tl
  | _ :: tl => theory_ctx_int tl
  | nil => nil
  end.

(*Unfolding the theory*)

(*We can unfold the "use" and "clone" definitions to get
  a simple theory with only definitions and goals/lemmas/axioms.
  We use a preprocessing step to turn all lemmas into
  axioms and remove goals
  TODO: do we still need context functions?
  TODO: do we need this?*)

(*Typing*)

(*Plan: have notion of well-typed theory (just that internal context
  is well-typed), will prob need to show that
  internal context well-typed => external context well-typed
  (this might be difficult, need to go in reverse direction)
  then show that we can check efficiently just by checking for
  name clashes (don't have to do anything else)

  after, give notion of valid_theory, in which we go through each 
  proof goal and generate task based on context (internal) and 
  previous axioms/lemmas - then valid iff all tasks are valid
  give as Inductive and Fixpoint (for generating goals) most likely
  *)



(*Typechecking*)

(*We want to check efficiently, not having to check the whole
  context. So we give an alternate definition of a typed theory,
  which we show is equivalent to the original one*)
(*  Print valid_context.
Require Import Typechecker.
Print tdecl.
(*Suppose we have already typechecked all of the
  external theories that we "use" and "clone".
  Then, we don't want to typecheck them again*)

(*TODO: for now, just typecheck things again. But
  we should REALLY go back and implemEquationsent this fully*)


Fixpoint check_typed_theory (t: theory) : bool :=
  match t with
  | nil => true
  | h :: tl =>
    check_typed_theory_tl &&
    match h with
    | tdef d =>
      (*TODO: expensive to get context every time*)
      check_context_cons d (theory_ctx_int t)
    | tprop p name f =>
      (*Typecheck prop formula - or TODO - do with valid?*)
      typecheck_formula f (theory_ctx_int t)
    | tuse th b =>
      (**)


    check_typed_theory_tl
  end.
*)

(*Valid theory*)

(*To show that a theory is valid, we generate a series of tasks
  in the way that we might expect: go through the theory and
  prove each lemma/goal, assuming all previous axioms/lemmas*)

Require Import Task.



(*Axioms/lemmas from a theory that can be used externally*)
Equations theory_axioms_ext (t: theory) : list (string * formula) 
  by wf (theory_size t) lt :=
(*Add lemmas and axioms from current theory*)
theory_axioms_ext (tprop Paxiom name f :: tl)  :=
  (name, f) :: theory_axioms_ext tl;
theory_axioms_ext (tprop Plemma name f :: tl) :=
  (name, f) :: theory_axioms_ext tl;
(*Add all from used that we export*)
theory_axioms_ext (tuse th true :: tl) :=
  theory_axioms_ext th ++ theory_axioms_ext tl;
(*Add all from cloning, after qualifying and substituting*)
theory_axioms_ext (tclone th o tys funs preds :: tl) :=
  let n := get_exported_names th in
  (*This also qualifies props*)
  let qual := 
    match o with | Some name => qualify_theory name n th | None => th end in
  sub_props_map tys funs preds (theory_axioms_ext qual) ++
  theory_axioms_ext tl;
(*No other lemmas/axioms*)
theory_axioms_ext nil := nil;
theory_axioms_ext (_ :: tl) := theory_axioms_ext tl.
Next Obligation.
subst qual. destruct o; try lia.
pose proof (qualify_theory_size s n th). 
unfold theory_size in *. lia.
Defined.

(*Difference - we are allowed to use theorems in "use"*)
Fixpoint theory_axioms_int (t: theory) : list (string * formula) :=
  match t with
  | tprop Paxiom name f :: tl =>
    (name, f) :: theory_axioms_int tl
  | tprop Plemma name f :: tl =>
    (name, f) :: theory_axioms_int tl
  | tuse th _ :: tl =>
    theory_axioms_ext th ++ theory_axioms_ext tl
  | tclone th o tys funs preds :: tl =>
    let n := get_exported_names th in
    let qual := 
      match o with | Some name => qualify_theory name n th | None => th end in
    sub_props_map tys funs preds (theory_axioms_ext qual) ++ 
    theory_axioms_int tl
  | _ :: tl => theory_axioms_int tl
  | nil => nil
  end.

(*Well-typed theory*)

(*Well-typed propositions*)
(*TODO: repeats existing, just like typing. OK for now*)
Equations typed_theory_p (t: theory) : Prop
by wf (theory_size t) lt :=
typed_theory_p nil := True;
typed_theory_p (tprop _ _ f :: tl) :=
  formula_typed (theory_ctx_int tl) f /\
  typed_theory_p tl;
typed_theory_p (tuse th _ :: tl) :=
  typed_theory_p th /\
  typed_theory_p tl;
typed_theory_p (tclone th _ _ _ _ :: tl) :=
  typed_theory_p th /\
  typed_theory_p tl;
typed_theory_p (tdef _ :: tl) := typed_theory_p tl.

(*A decidable version*)
Require Import Typechecker.
Equations check_typed_theory_p (t: theory) : bool
by wf (theory_size t) lt :=
check_typed_theory_p nil := true;
check_typed_theory_p (tprop _ _ f :: tl) :=
  typecheck_formula (theory_ctx_int tl) f &&
  check_typed_theory_p tl;
check_typed_theory_p (tuse th _ :: tl) :=
  check_typed_theory_p th &&
  check_typed_theory_p tl;
check_typed_theory_p (tclone th _ _ _ _ :: tl) :=
  check_typed_theory_p th &&
  check_typed_theory_p tl;
check_typed_theory_p (tdef _ :: tl) := check_typed_theory_p tl.

From mathcomp Require Import all_ssreflect.

Lemma check_typed_theory_p_spec t:
  reflect (typed_theory_p t) (check_typed_theory_p t) .
Proof.
  move: t.
  apply (typed_theory_p_elim (fun t1 P => reflect P (check_typed_theory_p t1)));
  rewrite /=; intros.
  - by apply ReflectT.
  - by rewrite check_typed_theory_p_equation_2.
  - rewrite check_typed_theory_p_equation_3.
    apply andPP =>//.
    by apply typecheck_formula_correct.
  - rewrite check_typed_theory_p_equation_4.
    by apply andPP.
  - rewrite check_typed_theory_p_equation_5.
    by apply andPP.
Qed.

Definition typed_theory (t: theory) : Prop :=
  valid_context (theory_ctx_int t) /\
  typed_theory_p t.

Definition check_typed_theory (t: theory) : bool :=
  check_context (theory_ctx_int t) && check_typed_theory_p t.

Lemma check_typed_theory_correct (t: theory) :
  reflect (typed_theory t) (check_typed_theory t).
Proof.
  apply andPP.
  - apply check_context_correct.
  - apply check_typed_theory_p_spec.
Qed.

(*Really, could give more useful error messages by looking
  at which part fails*)
Ltac check_theory :=
  apply /check_typed_theory_correct;
  reflexivity.

(*TODO: change in Denotational (generalize params)*)
Definition get_arg_list {gamma} (gamma_valid: valid_context gamma) 
  pd (v: val_typevar)
  (s: fpsym) (vs: list vty) (ts: list term) 
  (reps: forall (t: term) (ty: vty),
    term_has_type gamma t ty ->
    domain (dom_aux pd) (v_subst v ty))
  {args: list vty}
  {params: list typevar}
  (Hp: NoDup params)
  (Hlents: length ts = length args)
  (Hlenvs: length vs = length params)
  (Hall: Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine ts (map (ty_subst params vs) args))):
    arg_list (domain (dom_aux pd))
    (ty_subst_list_s params
      (map (v_subst v) vs) args).
Proof.
  generalize dependent args. induction ts; simpl; intros.
  - destruct args.
    + exact (@HL_nil _ _).
    + exact (False_rect _ (Nat.neq_0_succ (length args) Hlents)).
  - destruct args as [| a1 atl].
    + exact ( False_rect _ (Nat.neq_succ_0 (length ts) Hlents)).
    + exact ((HL_cons _ _ _ (dom_cast (dom_aux pd)
    (funsym_subst_eq params vs v a1
    Hp (Logic.eq_sym Hlenvs))
      (reps _ _ (Forall_inv Hall)))
       (IHts atl (*atl*) 
        (Nat.succ_inj (length ts) (length atl) Hlents)
        (Forall_inv_tail Hall)))).
Defined.

(*TODO: change in Denotational (strict generalization)*)

Lemma get_arg_list_vt_ext' {gamma} (gamma_valid: valid_context gamma) 
pd (pf: pi_funpred gamma_valid pd) 
(vt1 vt2: val_typevar) (s: fpsym)
  (vs1 vs2: list vty) (ts1 ts2: list term) vv1 vv2
  (reps1 reps2: forall (vt: val_typevar) (pf: pi_funpred gamma_valid pd) 
    (vv: val_vars pd vt)
    (t: term) (ty: vty) (Hty: term_has_type gamma t ty),
    domain (dom_aux pd) (v_subst vt ty))
  (Hts: length ts1 = length ts2)
  (Hreps: forall (i: nat),
    (i < length ts1)%coq_nat ->
    forall (ty1 ty2: vty) Hty1 Hty2 Heq,
      dom_cast (dom_aux pd) Heq 
        (reps1 vt1 pf vv1 (List.nth i ts1 tm_d) ty1 Hty1) =
      reps2 vt2 pf vv2 (List.nth i ts2 tm_d) ty2 Hty2)
  {args: list vty}
  {params: list typevar}
  (Hp: NoDup params)
  (Hlents1: length ts1 = length args)
  (Hlents2: length ts2 = length args)
  (Hlenvs1: length vs1 = length params)
  (Hlenvs2: length vs2 = length params)
  (Hall1: Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine ts1 (map (ty_subst params vs1) args)))
  (Hall2: Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine ts2 (map (ty_subst params vs2) args)))
  (Heq: map (v_subst vt1) vs1 = map (v_subst vt2) vs2):
  cast_arg_list 
    (f_equal (fun x => ty_subst_list_s params x args) Heq)
    (get_arg_list gamma_valid pd vt1 s vs1 ts1 (reps1 vt1 pf vv1) Hp Hlents1 Hlenvs1 Hall1) =
  get_arg_list gamma_valid pd vt2 s vs2 ts2 (reps2 vt2 pf vv2) Hp Hlents2 Hlenvs2 Hall2.
Proof.
  match goal with
  | |- cast_arg_list ?H ?a = _ => generalize dependent H end.
  clear Heq.
  unfold get_arg_list.
  generalize dependent args.
  generalize dependent ts2. 
  induction ts1; simpl; intros. 
  - destruct ts2; [|subst; inversion Hts].
    destruct args; simpl; auto; [|inversion Hlents1].
    assert (e = Logic.eq_refl). apply UIP_dec. apply list_eq_dec.
    apply sort_eq_dec. 
    subst. reflexivity.
  - destruct ts2; inversion Hts.
    destruct args.
    + inversion Hlents2.
    + simpl in Hlenvs2. simpl.
      simpl in e.
      rewrite (cast_arg_list_cons e).
      f_equal.
      * rewrite -> rewrite_dom_cast, !dom_cast_compose.
        assert (Heq': v_subst vt1 (ty_subst params vs1 v) = v_subst vt2 (ty_subst params vs2 v)). {
          rewrite !funsym_subst_eq; auto.
          apply (cons_inj_hd e).
        }
        erewrite <- (Hreps 0) with(Hty1:=Forall_inv Hall1)(Heq:=Heq'); try lia.
        rewrite !dom_cast_compose. apply dom_cast_eq.
      * apply IHts1; auto.
        intros i Hi ty Hty1 Hty2 Heq.
        apply (Hreps (S i) (ltac:(lia))).
Qed.

(*This defines what it means for a theory
  to be valid.
  We want to do the following
  1. Give a function that generates proof goals 
    to prove that a theory is valid
  2. Maybe give typeclasses to help with proving
    dependencies
  3. Prove that this definition implies that,
    for a given theory t and formula f,
    if we have (valid_theory (tprop Plemma/Pgoal _ f :: t)),
    then (theory_ctx_int t, theory_axioms t) |= f
    and as a corollary, if no axioms, then gamma, . |= f
    (more of a sanity check than anything else)*)

(*Monomoprhize goals if polymorphic*)

(*To prove that patterns are well-typed,
  we need a condition that the names of pattern variables
  are unique (not just the vsymbols). Really, this should
  be in typing, but it makes alpha equvialence much harder.
  For now, we have a separate condition, which we can check.
  We could alpha convert if needed to make this condition true*)
(*Give as bool*)
Section PatUniq.

Fixpoint pat_names_uniq (p:pattern) : Prop :=
  match p with
  | Pconstr f args ps =>
    Forall id (map pat_names_uniq ps) /\
    forall i j, (i < length ps)%coq_nat -> (j < length ps)%coq_nat ->
    i <> j ->
    forall x, ~ (In x (map fst (pat_fv (List.nth i ps Pwild))) /\
      In x (map fst (pat_fv (List.nth j ps Pwild))))
  | Por p1 p2 => pat_names_uniq p1 /\ pat_names_uniq p2
  | Pbind p x => pat_names_uniq p /\ ~ In (fst x) (map fst (pat_fv p))
  | _ => true
  end.

Fixpoint pat_names_uniqb (p: pattern) : bool :=
  match p with
  | Pconstr f args ps => 
    all id (map pat_names_uniqb ps) &&
    [forall x in 'I_(length ps), forall y in 'I_(length ps),
    (x != y) ==>  
    null (seqI (map fst (pat_fv (nth Pwild ps x))) 
      (map fst (pat_fv (nth Pwild ps y))))]
  | Por p1 p2 => pat_names_uniqb p1 && pat_names_uniqb p2
  | Pbind p x => pat_names_uniqb p && 
    ((fst x) \notin (map fst (pat_fv p)))
  | _ => true
  end.

Lemma all_Forall_idP {A: Type} (P: A -> Prop) (b: A -> bool)
  (l: list A):
  (forall x, In x l -> reflect (P x) (b x)) ->
  reflect (Forall id (map P l)) (all id (map b l)).
Proof.
  move=>Hrefl.
  apply iff_reflect. rewrite Forall_map all_map.
  apply reflect_iff.
  apply forallb_ForallP => x Hinx.
  by apply Hrefl.
Qed.

Lemma pat_names_uniqb_correct p:
  reflect (pat_names_uniq p) (pat_names_uniqb p).
Proof.
  apply 
    (pattern_rect (fun (p: pattern) => 
      reflect (pat_names_uniq p) (pat_names_uniqb p)))=>//=.
  - move=> _. by reflT.
  - (*The hard case*)
    move=> f vs ps Hall.
    have Hallr: reflect (Forall id [seq pat_names_uniq i | i <- ps])
      (all id [seq pat_names_uniqb i | i <- ps]).
    {
      apply all_Forall_idP.
      apply ForallT_In=>//. apply pattern_eq_dec. 
    }
    case: Hallr => Halluniq; last by reflF.
    case: [forall x in 'I_(Datatypes.length ps),
    forall y in 'I_(Datatypes.length ps),
    (x != y) ==>
    null (seqI (map fst(pat_fv (nth Pwild ps x))) 
      (map fst (pat_fv (nth Pwild ps y))))] 
    /forallP => Hforallx/=; last first.
    + apply ReflectF => [[_ C]]. apply Hforallx. move=> x.
      apply /implyP => _. apply /forallP => y.
      apply /implyP=>_. apply /implyP => Hneq.
      apply /nullP. apply /eqP. 
      rewrite /seqI -(negbK (_ == _)) -has_filter. 
      apply /negP => /hasP [z] /inP Hzin1 /inP Hzin2.
      apply (C x y (ltac:(by apply /ltP)) (ltac:(by apply /ltP))
        (ltac:(by apply /eqP)) z).
      by rewrite !nth_eq.
    + apply ReflectT. split=>//. move => i j /ltP Hi /ltP Hj /eqP Hij x.
      rewrite !nth_eq => [[Hinxi Hinxj]].
      move: Hforallx => /(_ (Ordinal Hi))/= /forallP 
        /(_ (Ordinal Hj))/= /implyP.
      have Hneq: (Ordinal (n:=Datatypes.length ps) (m:=i) Hi
        != Ordinal (n:=Datatypes.length ps) (m:=j) Hj).
      apply /eqP=> C. inversion C; subst. by rewrite eq_refl in Hij.
      move=>/(_ Hneq) /nullP /eqP. 
      rewrite /seqI -(negbK (_ == _)) -has_filter => /hasP.
      apply. by exists x; apply /inP.
  - by reflT.
  - move=> p1 p2 Hr1 Hr2. by apply andPP.
  - move=> p1 v Hr.
    apply andPP=>//.
    apply negPP. apply inP.
Qed.

(*Push through terms and formulas*)
Fixpoint pat_names_uniq_t (t: term) : Prop :=
  match t with
  | Tfun f tys tms => Forall id (map pat_names_uniq_t tms)
  | Tlet t1 v t2 => pat_names_uniq_t t1 /\ pat_names_uniq_t t2
  | Tif f t1 t2 => pat_names_uniq_f f /\ pat_names_uniq_t t1 /\
    pat_names_uniq_t t2
  | Tmatch t ty ps => pat_names_uniq_t t /\
    Forall id (map (fun x => pat_names_uniq (fst x) /\ pat_names_uniq_t (snd x)) ps)
  | Teps f x => pat_names_uniq_f f
  | _ => True
  end
with pat_names_uniq_f (f: formula) : Prop :=
  match f with
  | Fpred p tys tms => Forall id (map pat_names_uniq_t tms)
  | Fquant q v f => pat_names_uniq_f f
  | Feq ty t1 t2 => pat_names_uniq_t t1 /\ pat_names_uniq_t t2
  | Fbinop b f1 f2 => pat_names_uniq_f f1 /\ pat_names_uniq_f f2
  | Fnot f => pat_names_uniq_f f
  | Flet t1 v f => pat_names_uniq_t t1 /\ pat_names_uniq_f f
  | Fif f1 f2 f3 => pat_names_uniq_f f1 /\ pat_names_uniq_f f2 /\
    pat_names_uniq_f f3
  | Fmatch t ty ps => pat_names_uniq_t t /\
    Forall id (map (fun x => pat_names_uniq (fst x) /\ pat_names_uniq_f (snd x)) ps)
  | _ => True
  end.

Fixpoint pat_names_uniq_tb (t: term) : bool :=
  match t with
  | Tfun f tys tms => all id (map pat_names_uniq_tb tms)
  | Tlet t1 v t2 => pat_names_uniq_tb t1 && pat_names_uniq_tb t2
  | Tif f t1 t2 => pat_names_uniq_fb f && pat_names_uniq_tb t1 &&
    pat_names_uniq_tb t2
  | Tmatch t ty ps => pat_names_uniq_tb t &&
    all id (map (fun x => pat_names_uniqb (fst x) && pat_names_uniq_tb (snd x)) ps)
  | Teps f x => pat_names_uniq_fb f
  | _ => true
  end
with pat_names_uniq_fb (f: formula) : bool :=
  match f with
  | Fpred p tys tms => all id (map pat_names_uniq_tb tms)
  | Fquant q v f => pat_names_uniq_fb f
  | Feq ty t1 t2 => pat_names_uniq_tb t1 && pat_names_uniq_tb t2
  | Fbinop b f1 f2 => pat_names_uniq_fb f1 && pat_names_uniq_fb f2
  | Fnot f => pat_names_uniq_fb f
  | Flet t1 v f => pat_names_uniq_tb t1 && pat_names_uniq_fb f
  | Fif f1 f2 f3 => pat_names_uniq_fb f1 && pat_names_uniq_fb f2 &&
    pat_names_uniq_fb f3
  | Fmatch t ty ps => pat_names_uniq_tb t &&
    all id (map (fun x => pat_names_uniqb (fst x) && pat_names_uniq_fb (snd x)) ps)
  | _ => true
  end.

Lemma pat_names_uniq_b_correct (t: term) (f: formula):
  (reflect (pat_names_uniq_t t) (pat_names_uniq_tb t)) *
  (reflect (pat_names_uniq_f f) (pat_names_uniq_fb f)).
Proof.
  revert t f. apply term_formula_rect=>//=.
  - move=>_. by reflT.
  - move=>_. by reflT.
  - move=>_ _ tms Hall.
    apply all_Forall_idP.
    apply ForallT_In=>//. apply term_eq_dec.
  - move=>tm1 _ tm2 Hr1 Hr2.
    by apply andPP.
  - move=> f t1 t2 Hr1 Hr2 Hr3.
    rewrite -andbA.
    apply andPP=>//.
    by apply andPP.
  - move=> t _ ps Hr Hall.
    apply andPP=>//.
    apply all_Forall_idP=> x Hinx.
    apply andPP.
    + apply pat_names_uniqb_correct.
    + apply ForallT_In with(x:=snd x) in Hall=>//.
      apply term_eq_dec. rewrite in_map_iff.
      by exists x. 
  - move=>_ _ tms Hall.
    apply all_Forall_idP.
    apply ForallT_In=>//. apply term_eq_dec.
  - move=>_ t1 t2 Hr1 Hr2.
    by apply andPP.
  - move=>_ f1 f2 Hr1 Hr2.
    by apply andPP.
  - by reflT.
  - by reflT.
  - move=>t _ f Hr1 Hr2.
    by apply andPP.
  - move=>f1 f2 f3 Hr1 Hr2 Hr3.
    rewrite -andbA. by repeat apply andPP=>//.
  - move=> t _ ps Hr Hall.
    apply andPP=>//.
    apply all_Forall_idP=> x Hinx.
    apply andPP.
    + apply pat_names_uniqb_correct.
    + apply ForallT_In with(x:=snd x) in Hall=>//.
      apply formula_eq_dec. rewrite in_map_iff.
      by exists x.
Qed. 

End PatUniq.

Section Mono.

(*Idea: extend context with new type symbols, replace
  each type variable with one of these constants*)
(*Our type constants will be 'x0, 'x1, etc*)
Definition tyconstsym (n: string) : typesym :=
  mk_ts n nil.
Definition tyconst (n: string) : vty :=
  vty_cons (tyconstsym n) nil.
Definition tyconst_s (n: string) : Types.sort :=
  exist _ (tyconst n) Logic.eq_refl.

(*TODO: move*)
(*Substitue a type for a type variable in a term/formula*)
(*Definition ty_subst_single (ty: vty) (a: typevar) (v: vty) :=
  ty_subst' [a] [ty] v.*)

Definition ty_subst_list' (vs: list typevar) (ts: list vty) (l: list vty) :=
  map (ty_subst' vs ts) l.

Lemma valid_type_ty_subst': forall s ty vars tys,
  valid_type s ty ->
  Forall (valid_type s) tys ->
  valid_type s (ty_subst' vars tys ty).
Proof.
  intros.
  induction ty; simpl; auto.
  - destruct (in_dec typevar_eq_dec v vars); auto.
    apply valid_type_ty_subst; auto.
  - inversion H; subst. constructor; auto.
    rewrite map_length; auto.
    intros x. rewrite in_map_iff. intros [y [Hx Hiny]]; subst.
    rewrite Forall_forall in H1. apply H1; auto.
Qed.

Require Import Alpha.
Section TySubst.

Variable (params: list typevar) (tys: list vty).

Definition ty_subst_var (v: vsymbol) : vsymbol :=
  (fst v, ty_subst' params tys (snd v)).

(*Definition ty_subst_p := map_pat ty_subst_var.*)






Fixpoint ty_subst_p (p: pattern) : pattern :=
  match p with
  | Pvar x => Pvar (ty_subst_var x)
  | Pconstr f args ps => Pconstr f (ty_subst_list' params tys args)
    (map ty_subst_p ps)
  | Pwild => Pwild
  | Por p1 p2 => Por (ty_subst_p p1) (ty_subst_p p2)
  | Pbind p x => Pbind (ty_subst_p p) (ty_subst_var x)
  end.

Fixpoint ty_subst_tm  (t: term) : term :=
  match t with
  | Tconst c => Tconst c
  | Tvar v => Tvar (ty_subst_var v)
  | Tfun f args tms =>
    Tfun f (ty_subst_list' params tys args) (map ty_subst_tm tms)
  | Tlet t1 x t2 =>
    Tlet (ty_subst_tm  t1) (ty_subst_var x)
      (ty_subst_tm t2)
  | Tif f t1 t2 =>
    Tif (ty_subst_fmla f) (ty_subst_tm t1) (ty_subst_tm t2)
  | Tmatch t ty ps =>
    Tmatch (ty_subst_tm t) (ty_subst' params tys ty)
    (map (fun x => (ty_subst_p (fst x), ty_subst_tm (snd x))) ps)
  | Teps f x => Teps (ty_subst_fmla f) (ty_subst_var x)
  end
with ty_subst_fmla (f: formula) : formula :=
  match f with
  | Fpred p args tms => Fpred p (ty_subst_list' params tys args)
    (map ty_subst_tm tms)
  | Fquant q x f => Fquant q (ty_subst_var x) (ty_subst_fmla f)
  | Feq ty t1 t2 => Feq (ty_subst' params tys ty) (ty_subst_tm t1)
    (ty_subst_tm t2)
  | Fbinop b f1 f2 => Fbinop b (ty_subst_fmla f1) (ty_subst_fmla f2)
  | Fnot f => Fnot (ty_subst_fmla f)
  | Ftrue => Ftrue
  | Ffalse => Ffalse 
  | Flet t x f => Flet (ty_subst_tm t) (ty_subst_var x) (ty_subst_fmla f)
  | Fif f1 f2 f3 => Fif (ty_subst_fmla f1) (ty_subst_fmla f2)
    (ty_subst_fmla f3)
  | Fmatch t ty ps =>
   Fmatch (ty_subst_tm t) (ty_subst' params tys ty)
   (map (fun x => (ty_subst_p (fst x), ty_subst_fmla (snd x))) ps)
  end.

(*Typing*)
Context {gamma: context} (gamma_valid: valid_context gamma).
Variable (*(Hnodup: NoDup params) (Hlen: length params = length tys)*)
  (Hval: Forall (valid_type gamma) tys).

Lemma ty_subst_var_valid (v: vsymbol):
  valid_type gamma (snd v) ->
  valid_type gamma (snd (ty_subst_var v)).
Proof.
  destruct v; simpl. intros.
  apply valid_type_ty_subst'; auto.
Qed.

Lemma ty_subst_twice params1 tys1 params2 tys2 ty:
  NoDup params1 ->
  length params1 = length tys1 ->
  ty_subst' params2 tys2 (ty_subst params1 tys1 ty) =
  ty_subst params1 (ty_subst_list' params2 tys2 tys1) ty.
Proof.
  intros Hn1 Hlen1.
  unfold ty_subst_list', ty_subst.
  induction ty; simpl; auto.
  - destruct (in_dec typevar_eq_dec v params1).
    + destruct (In_nth _ _ EmptyString i) as [j [Hj Hv]]; subst.
      rewrite -> !ty_subst_fun_nth with (s:=s_int); auto; [| rewrite map_length; auto].
      rewrite -> map_nth_inbound with(d2:=vty_int); [| rewrite <- Hlen1; auto].
      reflexivity.
    + rewrite !ty_subst_fun_notin; auto. 
  - f_equal.
    apply list_eq_ext'; rewrite !map_length; auto.
    intros n d Hn'.
    rewrite -> !map_nth_inbound with (d2:=vty_int); auto;
    [| rewrite map_length; auto].
    rewrite Forall_forall in H. apply H. apply nth_In; auto.
Qed.

(*Lemma ty_subst_p_fv (p: pattern):
  pat_fv (ty_subst_p p) = map ty_subst_var (pat_fv p).
Proof.
  induction p; simpl; auto.
  - induction ps; simpl; intros; auto. inversion H; subst; simpl; auto.
    Check map_union.
    rewrite map_union.
    rewrite union_map. 
  
  Search big_union map.*)

Lemma ty_subst_p_fv (p: pattern):
(forall x, In x (pat_fv (ty_subst_p p)) <-> In x (map ty_subst_var (pat_fv p))).
Proof.
  intros. induction p; simpl; auto; try reflexivity.
  - simpl_set. rewrite in_map_iff.
    split.
    + intros [p [Hinp Hinx]].
      revert Hinp; rewrite in_map_iff.
      intros [p' [Hpeq Hinp']]; subst.
      rewrite Forall_forall in H.
      specialize (H _ Hinp').
      destruct H. specialize (H Hinx); clear H0.
      rewrite in_map_iff in H.
      destruct H as [x' [Hx Hinx']]; subst.
      exists x'. split; auto. simpl_set.
      exists p'; auto.
    + intros [x' [Hx Hinx']]; subst.
      revert Hinx'. simpl_set. intros [p [Hinp Hinx']].
      rewrite Forall_forall in H.
      specialize (H _ Hinp). destruct H.
      clear H. rewrite in_map_iff in H0.
      prove_hyp H0.
      { exists x'. split; auto. }
      exists (ty_subst_p p); split; auto.
      rewrite in_map_iff. exists p; auto.
  - simpl_set. rewrite IHp1 IHp2.
    rewrite !in_map_iff. split; intros; destruct_all; subst.
    + exists x0. split; auto; simpl_set; auto.
    + exists x0. split; auto; simpl_set; auto.
    + simpl_set. destruct H0; [left | right]; exists x0; auto.
  - simpl_set. rewrite IHp. rewrite !in_map_iff;
    split; intros; destruct_all; subst.
    + exists x0; simpl_set; auto.
    + exists v; simpl_set; auto.
    + simpl_set. destruct H0 as [Hinx1 | [Hxv | []]]; subst;
      [left | right]; auto.
      exists x0; auto.
Qed.

Lemma ty_subst_var_fst v1 v2:
  ty_subst_var v1 = ty_subst_var v2 ->
  fst v1 = fst v2.
Proof.
  unfold ty_subst_var; intros. inversion H; subst; auto.
Qed.
    
Lemma ty_subst_p_ty (p: pattern) (ty: vty)
  (Hp: pattern_has_type gamma p ty)
  (Hp2: pat_names_uniq p):
  pattern_has_type gamma (ty_subst_p p) (ty_subst' params tys ty).
  (*pat_fv (ty_subst_p p) = map ty_subst_var (pat_fv p).*)
Proof.
  generalize dependent ty.
  induction p; simpl; intros; inversion Hp; subst.
  - constructor. apply ty_subst_var_valid; auto.
  - subst sigma. rewrite ty_subst_twice; auto; [| apply s_params_Nodup].
    constructor; auto.
    + rewrite Forall_forall. intros x. rewrite in_map_iff.
      intros [y [Hy Hiny]]; subst.
      apply valid_type_ty_subst'; auto.
      rewrite Forall_forall in H4. apply H4; auto.
    + rewrite map_length; auto.
    + rewrite map_length; auto.
    + intros x. rewrite in_combine_iff; rewrite !map_length; auto.
      intros [i [Hi Hx]]. specialize (Hx Pwild vty_int); subst; simpl.
      rewrite -> !map_nth_inbound with(d2:=vty_int); try lia.
      rewrite -> map_nth_inbound with (d2:=Pwild); auto.
      rewrite Forall_forall in H.
      rewrite <- ty_subst_twice; auto; [| apply s_params_Nodup].
      apply H; [apply nth_In; auto| |].
      * simpl in Hp2. destruct Hp2.
        rewrite Forall_map in H0.
        rewrite Forall_forall in H0. apply H0. apply nth_In; auto.
      * apply (H10 (List.nth i ps Pwild,  (ty_subst (s_params f) vs (List.nth i (s_args f) vty_int)))).
        rewrite in_combine_iff; try rewrite !map_length; auto.
        exists i. split; auto. intros.
        f_equal; try apply nth_indep; auto.
        rewrite -> map_nth_inbound with (d2:=vty_int); auto; lia.
    + rewrite !map_length. intros.
      rewrite -> !map_nth_inbound with (d2:=Pwild); auto.
      rewrite !ty_subst_p_fv.
      rewrite -> !in_map_iff; intros [Hex1 Hex2]; destruct_all; subst.
      (*Here, we need the assumption - types may be same but names cannot*)
      apply ty_subst_var_fst in H7.
      simpl in Hp2.
      destruct Hp2 as [_ Hdisj].
      apply (Hdisj i j H0 H1 H2 (fst x0)).
      split; rewrite in_map_iff; [exists x1 | exists x0]; auto.
  - constructor. apply valid_type_ty_subst'; auto.
  - simpl in Hp2. destruct Hp2. constructor.
    + apply IHp1; auto.
    + apply IHp2; auto.
    + intros. rewrite !ty_subst_p_fv.
      rewrite !in_map_iff; split; intros; destruct_all; exists x0;
      split; auto; apply H5; auto.
  - simpl in Hp2. destruct Hp2.
    constructor.
    + rewrite ty_subst_p_fv in_map_iff; intros C; destruct_all.
      apply H0. rewrite in_map_iff. exists x; split; auto.
      apply ty_subst_var_fst; auto.
    + apply IHp; auto.
Qed.

Lemma ty_subst_tf_ty (t: term) (f: formula):
  (forall ty (Hty: term_has_type gamma t ty)
    (Hp: pat_names_uniq_t t),
    term_has_type gamma (ty_subst_tm t) (ty_subst' params tys ty)) /\
  (forall (Hty: formula_typed gamma f)
    (Hp: pat_names_uniq_f f),
    formula_typed gamma (ty_subst_fmla f)).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  inversion Hty; subst; try solve[unfold ty_subst; simpl; constructor];
  try solve[destruct_all; constructor; auto;
    try apply ty_subst_var_valid; auto; solve[intuition]].
  (*Only Fun/Pred, Match are nontrivial*)
  - (*Function is tricky case, but simpler than pattern constr*) 
    rewrite ty_subst_twice; auto; [| apply s_params_Nodup].
    constructor; auto.
    + rewrite Forall_forall; intros.
      unfold ty_subst_list in H0.
      rewrite in_map_iff in H0. destruct H0 as [ty [Hx Hinty]]; subst.
      apply valid_type_ty_subst'; auto. rewrite Forall_forall in H4.
      apply H4; auto.
    + rewrite map_length; auto.
    + rewrite map_length; auto.
    + revert H10 H. rewrite !Forall_forall; intros.
      revert H0.
      rewrite in_combine_iff; rewrite !map_length; auto.
      intros [i [Hi Hx]]; subst. specialize (Hx tm_d vty_int); subst;
      simpl.
      rewrite -> !map_nth_inbound with (d2:=vty_int); try lia.
      rewrite -> !map_nth_inbound with (d2:=tm_d); auto.
      rewrite <- ty_subst_twice; auto; [| apply s_params_Nodup].
      apply H; auto.
      * apply nth_In; auto.
      * apply (H10 ((nth i l1 tm_d), (ty_subst (s_params f1) l (nth i (s_args f1) vty_int)))).
        rewrite in_combine_iff; [| rewrite map_length; auto].
        exists i. split; auto.
        intros. rewrite -> !map_nth_inbound with (d2:=vty_int); try lia.
        f_equal. apply nth_indep; auto.
      * rewrite Forall_map in Hp.
        rewrite Forall_forall in Hp. apply Hp. apply nth_In; auto.
  -(*Match relies on pattern typing, rest is easy*) 
    destruct Hp as [Hpt Hallp].
    constructor; auto.
    + destruct H4 as [a [m [args [m_in [a_in Hv]]]]]; subst.
      exists a. exists m. exists (ty_subst_list' params tys args).
      split_all; auto.
    + intros x. rewrite in_map_iff. intros [x1 [Hx Hinx1]]; subst. simpl.
      apply ty_subst_p_ty; auto. rewrite Forall_map in Hallp.
      rewrite Forall_forall in Hallp. apply Hallp; auto.
    + intros x. rewrite in_map_iff. intros [x1 [Hx Hinx1]]; subst; simpl.
      rewrite Forall_forall in H0.
      apply H0; auto.
      * rewrite in_map_iff. exists x1; auto.
      * rewrite Forall_map Forall_forall in Hallp.
        apply Hallp; auto.
    + rewrite null_map. auto.
  - (*Pred almost same as Fun*) constructor; auto.
    + rewrite Forall_forall; intros.
      unfold ty_subst_list in H0.
      rewrite in_map_iff in H0. destruct H0 as [ty [Hx Hinty]]; subst.
      apply valid_type_ty_subst'; auto. rewrite Forall_forall in H4.
      apply H4; auto.
    + rewrite map_length; auto.
    + rewrite map_length; auto.
    + revert H8 H. rewrite !Forall_forall; intros.
      revert H0.
      rewrite in_combine_iff; rewrite !map_length; auto.
      intros [i [Hi Hx]]; subst. specialize (Hx tm_d vty_int); subst;
      simpl.
      rewrite -> !map_nth_inbound with (d2:=vty_int); try lia.
      rewrite -> !map_nth_inbound with (d2:=tm_d); auto.
      rewrite <- ty_subst_twice; auto; [| apply s_params_Nodup].
      apply H; auto.
      * apply nth_In; auto.
      * apply (H8 ((nth i tms tm_d), (ty_subst (s_params p) tys0 (nth i (s_args p) vty_int)))).
        rewrite in_combine_iff; [| rewrite map_length; auto].
        exists i. split; auto.
        intros. rewrite -> !map_nth_inbound with (d2:=vty_int); try lia.
        f_equal. apply nth_indep; auto.
      * rewrite Forall_map in Hp.
        rewrite Forall_forall in Hp. apply Hp. apply nth_In; auto.
  - (*Exact same proof*) destruct Hp as [Hpt Hallp].
    constructor; auto.
    + destruct H4 as [a [m [args [m_in [a_in Hv]]]]]; subst.
      exists a. exists m. exists (ty_subst_list' params tys args).
      split_all; auto.
    + intros x. rewrite in_map_iff. intros [x1 [Hx Hinx1]]; subst. simpl.
      apply ty_subst_p_ty; auto. rewrite Forall_map in Hallp.
      rewrite Forall_forall in Hallp. apply Hallp; auto.
    + intros x. rewrite in_map_iff. intros [x1 [Hx Hinx1]]; subst; simpl.
      rewrite Forall_forall in H0.
      apply H0; auto.
      * rewrite in_map_iff. exists x1; auto.
      * rewrite Forall_map Forall_forall in Hallp.
        apply Hallp; auto.
    + rewrite null_map. auto.
Qed.

Definition ty_subst_t_ty t := proj_tm ty_subst_tf_ty t.
Definition ty_subst_f_ty f := proj_fmla ty_subst_tf_ty f.

(*Part 2: reps for ty substitution.
  Much like term variable substitution, this corresponds
  to a change in valuation. Because it changes vt, 
  this induces annoying cast issues*)
Print upd_vv_args.

Variable (params_len: length params = length tys)
  (params_nodup: NoDup params).

Lemma params_len' vt: length params = length (map (v_subst vt) tys).
Proof.
  rewrite map_length; auto.
Qed.

Lemma v_subst_aux_twice f ty:
  (forall x, is_sort (f x)) ->
  v_subst_aux f (v_subst_aux f ty) =
  v_subst_aux f ty.
Proof.
  intros Hsort.
  induction ty; simpl; auto.
  rewrite <- subst_is_sort_eq; auto.
  f_equal. rewrite <- map_comp.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn.
  rewrite -> !map_nth_inbound with (d2:=vty_int); auto.
  rewrite Forall_forall in H. apply H.
  apply nth_In; auto.
Qed.

Lemma v_subst_vt_with_args' vt (v: vty):
  v_subst vt (ty_subst' params tys v) =
  v_subst (vt_with_args vt params (map (v_subst vt) tys)) v.
Proof.
  rewrite v_subst_vt_with_args; auto. 2: exact (params_len' _).
  unfold ty_subst_var. simpl.
  (*Idea: typevars assigned vt, either now or later*)
  induction v; simpl; auto.
  - destruct (in_dec typevar_eq_dec v params); auto.
    destruct (In_nth _ _ EmptyString i) as [j [Hj Hx]]; subst.
    apply sort_inj; simpl.
    unfold ty_subst. simpl.
    rewrite -> !ty_subst_fun_nth with(s:=s_int); auto;
    [| rewrite !map_length; auto].
    unfold sorts_to_tys.
    rewrite -> !map_nth_inbound with (d2:=s_int);
    [| rewrite map_length -params_len; auto].
    rewrite -> map_nth_inbound with (d2:=vty_int);
    [| rewrite -params_len; auto].
    simpl.
    rewrite v_subst_aux_twice; auto.
    intros. destruct (vt x); auto.
  - apply sort_inj; simpl. f_equal.
    rewrite <- !map_comp.
    apply list_eq_ext'; rewrite !map_length; auto.
    intros n d Hn.
    rewrite -> !map_nth_inbound with (d2:=vty_int); auto.
    rewrite Forall_forall in H.
    simpl.
    specialize (H (nth n vs vty_int) (ltac:(apply nth_In; auto))).
    inversion H; auto.
Qed.
(*Lemma v_subst_vt_with_args' vt (x: vsymbol):
  v_subst vt (ty_subst_var x).2 =
  v_subst (vt_with_args vt params (map (v_subst vt) tys)) x.2.
Proof.
  unfold ty_subst_var. simpl.
  rewrite v_subst_vt_with_args; auto. 2: exact (params_len' _).
  unfold ty_subst_var. simpl.
  (*Idea: typevars assigned vt, either now or later*)
  induction (x.2); simpl; auto.
  - destruct (in_dec typevar_eq_dec v params); auto.
    destruct (In_nth _ _ EmptyString i) as [j [Hj Hx]]; subst.
    apply sort_inj; simpl.
    unfold ty_subst. simpl.
    rewrite -> !ty_subst_fun_nth with(s:=s_int); auto;
    [| rewrite !map_length; auto].
    unfold sorts_to_tys.
    rewrite -> !map_nth_inbound with (d2:=s_int);
    [| rewrite map_length -params_len; auto].
    rewrite -> map_nth_inbound with (d2:=vty_int);
    [| rewrite -params_len; auto].
    simpl.
    rewrite v_subst_aux_twice; auto.
    intros. destruct (vt x0); auto.
  - apply sort_inj; simpl. f_equal.
    rewrite <- !map_comp.
    apply list_eq_ext'; rewrite !map_length; auto.
    intros n d Hn.
    rewrite -> !map_nth_inbound with (d2:=vty_int); auto.
    rewrite Forall_forall in H.
    simpl.
    specialize (H (nth n vs vty_int) (ltac:(apply nth_In; auto))).
    inversion H; auto.
Qed.*)

(*TODO: change original definition*)
Definition upd_vv_args' pd (vt: val_typevar) (vv: val_vars pd vt)
  p1 a1 (Hlen: length p1 = length a1)
  (Hn: NoDup p1):
  val_vars pd (vt_with_args vt p1 a1) :=
  fun x =>
  (dom_cast (dom_aux pd) 
    (Logic.eq_sym (v_subst_vt_with_args vt p1 a1 (snd x) Hlen Hn))
    (vv (fst x, ty_subst' p1 (sorts_to_tys a1) (snd x)))).

(*Why don't we just define it the way we want?*)
Definition upd_vv_args'' pd (vt: val_typevar) (vv: val_vars pd vt):
  val_vars pd (vt_with_args vt params (map (v_subst vt) tys)) :=
  fun x => 
  (dom_cast (dom_aux pd) (v_subst_vt_with_args' vt (snd x)) 
    (vv (ty_subst_var x))).

(*TODO: these are good, move*)
(*
Lemma map_v_subst_sorts vt srts:
  map (v_subst vt) (sorts_to_tys srts) = srts.
Proof.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn. unfold sorts_to_tys.
  rewrite -> !map_nth_inbound with (d2:=vty_int); auto;
  [| rewrite map_length; auto].
  rewrite -> map_nth_inbound with (d2:=s_int); auto.
  apply sort_inj; simpl.
  rewrite <- subst_is_sort_eq; auto.
  f_equal.
  apply nth_indep. auto.
  destruct (nth n srts s_int); auto.
Qed.


Definition upd_vv_args_alt
  (params: list typevar) (srts: list sort)
  (lengths_eq: length params = length srts)
  (nodup_params: NoDup params)
  pd vt (vv: val_vars pd vt):
  val_vars pd (vt_with_args vt params srts) :=
  fun x =>
  dom_cast (dom_aux pd) 
    (f_equal (fun y => v_subst (vt_with_args vt params y) x.2) 
      (map_v_subst_sorts vt srts))
    (upd_vv_args'' params (sorts_to_tys srts) 
    (eq_trans lengths_eq (Logic.eq_sym (map_length _ _))) nodup_params pd vt vv x).
*)

(*End good*)

(*This lemma is still not provable (and may not be true).
  We should use the above, and let's see what we need for 
  function unfolding*)
  (*
Lemma upd_vv_args_alt_equiv params tys params_len params_nodup pd (vt: val_typevar) (vv: val_vars pd vt)
x:
upd_vv_args_alt params (map (v_subst vt) tys) (params_len' params tys params_len vt) params_nodup pd vt vv  
   x =
dom_cast (dom_aux pd) 
  (v_subst_vt_with_args' params tys params_len params_nodup vt x)
  (*(Logic.eq_sym (v_subst_vt_with_args vt params (map (v_subst vt) tys)
    (snd x) (params_len' _) params_nodup)) *)
  (vv (ty_subst_var params tys x)).
Proof.
  unfold upd_vv_args_alt, upd_vv_args''.

  generalize dependent (map_v_subst_sorts vt (map (v_subst vt) tys)).
  generalize dependent (sorts_to_tys (map (v_subst vt) tys)).
  rewrite !dom_cast_compose.
  match goal with
  | |- dom_cast ?d ?H1 ?x1 = dom_cast ?d ?H2 ?x2 =>
    generalize dependent H1;
    generalize dependent H2
  end.
  (*Why we use this version: Only have equality of v_subst with
    others, not underlying types*)
  replace (sorts_to_tys (map (v_subst vt) tys)) with tys.
  intros. apply dom_cast_eq.

  rewrite map_v_subst_sorts.
  assert (tys = )
  generalize dependent 
  generalize dependent (ty_subst_var params tys x).
  assert ()


  rewrite map_v_subst_sorts.



Lemma upd_vv_args_alt_eq 
*)

 (* unfold val_vars.
  intros Hlen Hparams. unfold val_vars in vv.
  intros x. rewrite (v_subst_vt_with_args vt params args); 
    [| exact Hlen | exact Hparams].
  (*Is this a hack? Kind of*) apply (vv 
    (fst x, (ty_subst' params (sorts_to_tys args) (snd x)))).
Defined.*)
(*
Lemma dom_cast_eq d {A: Type} (g: A -> sort) 
  (f: forall (x: A), domain d (g x)) x1 x2
  (H1: g x1 = g x2):
  dom_cast d H1 (f x1) = f x2.
Proof.
  revert H1.
  unfold dom_cast. 
  intros. generalize dependent (f_equal (domain d) H1).
  intros. unfold scast. clear.
  generalize dependent (g x2).
  
  revert H1. destruct e. generalize dependent (g x1). generalize dependent (domain d (g x2)).
  generalize dependent (g x2).
*)
(*
Lemma scast_eq' {A: Set} {B: A -> Set} (x1 x2: A)
  (f: forall (x: A), B x)
  (Hf: f x1 = f x2):
  scast Hf (f x1) = f x2.
  scast H1 x1 = scast H2 x2*)

(*Lemma scast_eq {A B: Set} (H: A = B) (x1: A) (x2: B):
  scast H x1 = x2.*)

  (*Is this even true? The types are not the same (I think) only 
    after v_subst, so, dont think true
      ex: a -> int,
        vv (x, int) and vv (x, a) not necessarily same
        even if vt sends a -> int *)
(*
Lemma upd_vv_args_equiv pd (vt: val_typevar) (vv: val_vars pd vt)
  x:
  (upd_vv_args' pd vt vv params (map (v_subst vt) tys) 
      (params_len' _) params_nodup) x =
  dom_cast (dom_aux pd) 
    (v_subst_vt_with_args' vt x)
    (*(Logic.eq_sym (v_subst_vt_with_args vt params (map (v_subst vt) tys)
      (snd x) (params_len' _) params_nodup)) *)
    (vv (ty_subst_var x)).
Proof.
  unfold upd_vv_args'.
  generalize dependent (v_subst_vt_with_args' vt x).
  intros.
  generalize dependent (v_subst_vt_with_args vt params (map (v_subst vt) tys) x.2 
  (params_len' vt) params_nodup).
  intros.
  generalize dependent (v_subst (vt_with_args vt params (map (v_subst vt) tys)) x.2);
  intros. unfold dom_cast at 2; simpl.
  unfold ty_subst_var in *. simpl in *.
  generalize dependent (Logic.eq_sym e0). clear e0.
  intros.
  generalize dependent (ty_subst' params (sorts_to_tys (map (v_subst vt) tys)) x.2).
  generalize dependent ((ty_subst' params tys x.2)).
  intros; subst. simpl.
  
  assert (vv (x.1, v0) = dom_cast (dom_aux pd) (Logic.eq_sym e0) (vv(x.1, v))).
  unfold dom_cast. 
  revert e. rewrite <- e0.
  unfold dom_cast; simpl.
  generalize dependent (v_subst vt (ty_subst' params (sorts_to_tys (map (v_subst vt) tys)) x.2)).

  clear e0. rewrite <- e.
  rewrite e0.
  revert e.
  rewrite e0.
  revert e0. rewrite <- e.
  generalize dependent e. rewrite e0.
  generalize dependent (v_subst vt (ty_subst_var x).2).
  unfold ty_subst_var.

  rewrite e0.
  generalize vv. unfold val_vars.
  rewrite e0.
  Print val_vars.
  assert (e0 = )
  symmetry in e, e0.
  subst.
  Print Ltac subst.
  
  subst s. unfold dom_cast. simpl.
  unfold ty_subst_var.
  generalize dependent (ty_subst' params (sorts_to_tys (map (v_subst vt) tys)) x.2).
  intros.
  generalize dependent (v_subst vt v).
  generalize dependent ((ty_subst_var x).2).


  subst. unfold dom_cast. simpl.
  generalize dependent (v_subst vt (ty_subst_var x).2).
  unfold ty_subst_var.
  unfold eq_rec_r, dom_cast, scast. simpl.
  unfold ty_subst_var in Heq. simpl in Heq.
  Check (v_subst_vt_with_args vt params (map (v_subst vt) tys)
  (snd x) (params_len' _) params_nodup).


  vv (ty_subst_var x) = dom_cast (dom_aux pd) 
    (v_subst_vt_with_args vt params (map (v_subst vt) tys)
      (snd x) )
     ( ).*)

(*I think: we do need all bnd var names uniq*)
(*y is in free vars, hmm think*)

(*Lemma upd_vv_args_substi pd vt vv v x Heq y l:
  In y l ->
  NoDup (map fst l) ->
  upd_vv_args'' pd vt (substi pd vt vv (ty_subst_var v) 
    (dom_cast (dom_aux pd) Heq x)) y =
  substi pd (vt_with_args vt params (map (v_subst vt) tys))
    (upd_vv_args'' pd vt vv) v x y.
Proof.
  intros.
  unfold substi, upd_vv_args''.
  destruct (in_dec )
  vsym_eq y v.
  - vsym_eq (ty_subst_var v) (ty_subst_var v).
    simpl.
    assert (e = Logic.eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
    subst. simpl. rewrite -> dom_cast_compose, dom_cast_refl; auto.
  - 
  vsym_eq (ty_subst_var y) (ty_subst)


upd_vv_args'' pd vt
  (substi pd vt vv (ty_subst_var v)
     (dom_cast (dom_aux pd) Heq1
        (term_rep gamma_valid pd (vt_with_args vt params (map (v_subst vt) tys)) pf
           (upd_vv_args'' pd vt vv) tm1 v.2 (proj1' (ty_let_inv Hty1))))) x =
substi pd (vt_with_args vt params (map (v_subst vt) tys)) (upd_vv_args'' pd vt vv) v
  (term_rep gamma_valid pd (vt_with_args vt params (map (v_subst vt) tys)) pf
     (upd_vv_args'' pd vt vv) tm1 v.2 (proj1' (ty_let_inv Hty1))) x
*)
(*Think we need: no names in common among free vars
  AND no names in common between free and bound vars*)

(*We use a much stronger version of well-formedness:
  No free variables have any names in common, and no
  bound variables have names in common with free variables.
  This doesn't cause problems, because all formulas we work
  with are closed (or function bodies which have this restriction),
  so we can always alpha-convert and do this.
  TODO: actually, we can use alpha conversion in the proof,
  so we prove for well-formed then relax that assumption by
  alpha converting*)

  Ltac simpl_forall :=
    repeat match goal with
    | H: Forall ?P nil |- _ => clear H
    | H: Forall ?P (?x :: ?y) |- _ => inversion H; subst; clear H
    | H: Forall ?P (concat ?l) |- _ => rewrite Forall_concat in H
    | H: Forall ?P (map ?f ?l) |- _ => rewrite Forall_map in H
    | H: Forall ?P (?l1 ++ ?l2) |- _ => rewrite Forall_app in H;
      destruct H
    | H: Forall ?P (?l1 ++ ?l2)%list |- _ => rewrite Forall_app in H;
      destruct H
    | |- Forall ?P (map ?f ?l) => rewrite Forall_map
    end.

(*Our stronger notion*)
(*TODO: redo above (maybe others) with this*)
Section RecHolds.

Variable P_p: pattern -> Prop.
Variable P_t: term -> Prop.
Variable P_f: formula -> Prop.

(*A condition recursively holds on all subterms and subformulas*)

Fixpoint P_subpat (p: pattern) : Prop :=
  P_p p /\
  match p with
  | Pconstr _ _ ps => Forall id (map P_subpat ps)
  | Por p1 p2 => P_subpat p1 /\ P_subpat p2
  | Pbind p v => P_subpat p
  | _ => True
  end.

(*2 methods of this*)
(*First, recursively holds*)

Fixpoint P_subtm (t: term) : Prop :=
  P_t t /\
  match t with
  | Tfun _ _ tms => Forall id (map P_subtm tms)
  | Tlet t1 _ t2 => P_subtm t1 /\ P_subtm t2
  | Tif f t1 t2 => P_subfmla f /\ P_subtm t1 /\ P_subtm t2
  | Tmatch t _ ps =>
    P_subtm t /\
    Forall id (map (fun x => P_subpat (fst x) /\ P_subtm (snd x)) ps)
  | Teps f _ => P_subfmla f
  | _ => True
  end
with P_subfmla (f: formula) : Prop :=
  P_f f /\
  match f with
  | Fpred _ _ tms => Forall id (map P_subtm tms)
  | Feq _ t1 t2 => P_subtm t1 /\ P_subtm t2
  | Fbinop _ f1 f2 => P_subfmla f1 /\ P_subfmla f2
  | Fnot f => P_subfmla f
  | Flet t1 _ f2 => P_subtm t1 /\ P_subfmla f2
  | Fif f1 f2 f3 => P_subfmla f1 /\ P_subfmla f2 /\ P_subfmla f3
  | Fmatch t _ ps =>
    P_subtm t /\
    Forall id (map (fun x => P_subpat (fst x) /\ P_subfmla (snd x)) ps)
  | _ => True
  end.

(*Second: get all subterms/patterns/formulas*)
Fixpoint subpats (p: pattern) : list pattern :=
  p ::
  match p with
  | Pconstr _ _ ps => concat (map subpats ps)
  | Por p1 p2 => subpats p1 ++ subpats p2
  | Pbind p _ => subpats p
  | _ => nil
  end.

Fixpoint subterms_t (t: term) : list term :=
  t :: 
  match t with
  | Tfun _ _ tms => concat (map subterms_t tms)
  | Tlet t1 _ t2 => subterms_t t1 ++ subterms_t t2
  | Tif f t1 t2 => subterms_f f ++ subterms_t t1 ++ subterms_t t2
  | Tmatch t _ ps => subterms_t t ++ 
    concat (map (fun x => subterms_t (snd x)) ps)
  | Teps f _ => subterms_f f
  | _ => nil
  end
with subterms_f (f: formula) : list term :=
  match f with
  | Fpred _ _ tms => concat (map subterms_t tms)
  | Feq _ t1 t2 => subterms_t t1 ++ subterms_t t2
  | Fbinop _ f1 f2 => subterms_f f1 ++ subterms_f f2
  | Fnot f => subterms_f f
  | Flet t1 _ f2 => subterms_t t1 ++ subterms_f f2
  | Fif f1 f2 f3 => subterms_f f1 ++ subterms_f f2 ++ subterms_f f3
  | Fmatch t _ ps =>
    subterms_t t ++
    concat (map (fun x => subterms_f (snd x)) ps)
  | _ => nil
  end.

Fixpoint subfmla_t (t: term) : list formula :=
  match t with
  | Tfun _ _ tms => concat (map subfmla_t tms)
  | Tlet t1 _ t2 => subfmla_t t1 ++ subfmla_t t2
  | Tif f t1 t2 => subfmla_f f ++ subfmla_t t1 ++ subfmla_t t2
  | Tmatch t _ ps => subfmla_t t ++ 
    concat (map (fun x => subfmla_t (snd x)) ps)
  | Teps f _ => subfmla_f f
  | _ => nil
  end
with subfmla_f (f: formula) : list formula :=
  f ::
  match f with
  | Fpred _ _ tms => concat (map subfmla_t tms)
  | Feq _ t1 t2 => subfmla_t t1 ++ subfmla_t t2
  | Fbinop _ f1 f2 => subfmla_f f1 ++ subfmla_f f2
  | Fnot f => subfmla_f f
  | Flet t1 _ f2 => subfmla_t t1 ++ subfmla_f f2
  | Fif f1 f2 f3 => subfmla_f f1 ++ subfmla_f f2 ++ subfmla_f f3
  | Fmatch t _ ps =>
    subfmla_t t ++
    concat (map (fun x => subfmla_f (snd x)) ps)
  | _ => nil
  end.

Fixpoint subpat_t (t: term) : list pattern :=
  match t with
  | Tfun _ _ tms => concat (map subpat_t tms)
  | Tlet t1 _ t2 => subpat_t t1 ++ subpat_t t2
  | Tif f t1 t2 => subpat_f f ++ subpat_t t1 ++ subpat_t t2
  | Tmatch t _ ps => subpat_t t ++ 
    concat (map (fun x => subpats (fst x) ++ subpat_t (snd x)) ps)
  | Teps f _ => subpat_f f
  | _ => nil
  end
with subpat_f (f: formula) : list pattern :=
  match f with
  | Fpred _ _ tms => concat (map subpat_t tms)
  | Feq _ t1 t2 => subpat_t t1 ++ subpat_t t2
  | Fbinop _ f1 f2 => subpat_f f1 ++ subpat_f f2
  | Fnot f => subpat_f f
  | Flet t1 _ f2 => subpat_t t1 ++ subpat_f f2
  | Fif f1 f2 f3 => subpat_f f1 ++ subpat_f f2 ++ subpat_f f3
  | Fmatch t _ ps =>
    subpat_t t ++
    concat (map (fun x => subpats (fst x) ++ subpat_f (snd x)) ps)
  | _ => nil
  end.

Lemma Forall_apply {A: Type} {P Q: A -> Prop} {l}:
  Forall P l ->
  Forall (fun x => P x -> Q x) l ->
  Forall Q l.
Proof.
  rewrite !Forall_forall; intros; auto.
Qed.

Lemma Forall_impl_in  {A: Type} {P Q: A -> Prop} {l}:
(forall x, In x l -> P x -> Q x) ->
Forall P l ->
Forall Q l.
Proof.
  rewrite !Forall_forall; intros; auto.
Qed.

Lemma P_sub_pat_equiv1 p (Hsub: P_subpat p):
  Forall P_p (subpats p).
Proof.
  induction p; simpl in *; destruct_all; try solve[repeat (constructor; auto)].
  - constructor; auto. rewrite -> Forall_concat, Forall_map.
    rewrite Forall_map in H1.
    apply Forall_apply in H; auto.
  - constructor; auto. rewrite Forall_app; split; auto.
Qed.

Lemma P_sub_equiv1 t f: 
  (forall (Hsub: P_subtm t), Forall P_t (subterms_t t) /\
  Forall P_f (subfmla_t t) /\ Forall P_p (subpat_t t)) /\
  (forall (Hsub: P_subfmla f), Forall P_t (subterms_f f) /\
  Forall P_f (subfmla_f f) /\ Forall P_p (subpat_f f)).
Proof.
  revert t f; apply term_formula_ind; simpl; intros;
  destruct_all; try solve[split_all; repeat (constructor; auto)];
  try solve[intuition; try constructor; auto; rewrite !Forall_app; auto ].
  - rewrite Forall_map in H1.
    apply Forall_apply in H; auto; split_all; [constructor; auto | |];
    rewrite -> !Forall_concat, !Forall_map;
    revert H; apply Forall_impl; intros a Hall; apply Hall.
  - rewrite Forall_map in H3.
    apply Forall_apply in H0; [|revert H3; rewrite Forall_map; apply Forall_impl;
      intros a Ha; apply Ha].
    intuition; try constructor; auto; rewrite !Forall_app; split_all; auto;
    rewrite -> Forall_concat, Forall_map; revert H0; rewrite Forall_map; 
    apply Forall_impl_in;
    intros a Hina Ha; try rewrite Forall_app; try split; auto; try apply Ha.
    apply P_sub_pat_equiv1. rewrite Forall_forall in H3; apply H3; auto.
  - rewrite Forall_map in H1.
    apply Forall_apply in H; auto; split_all; [|constructor; auto |];
    rewrite -> !Forall_concat, !Forall_map;
    revert H; apply Forall_impl; intros a Hall; apply Hall.
  - rewrite Forall_map in H3.
    apply Forall_apply in H0; [|revert H3; rewrite Forall_map; apply Forall_impl;
      intros a Ha; apply Ha].
    intuition; try constructor; auto; rewrite !Forall_app; split_all; auto;
    rewrite -> Forall_concat, Forall_map; revert H0; rewrite Forall_map; 
    apply Forall_impl_in;
    intros a Hina Ha; try rewrite Forall_app; try split; auto; try apply Ha.
    apply P_sub_pat_equiv1. rewrite Forall_forall in H3; apply H3; auto.
Qed.



Lemma P_sub_pat_equiv2 p (Hp: Forall P_p (subpats p)):
  P_subpat p.
Proof.
  induction p; simpl in *; simpl_forall; split; auto; simpl_forall.
  repeat (apply Forall_apply in H; auto).
Qed.

Lemma P_sub_equiv2 t f: 
  (forall (Ht: Forall P_t (subterms_t t))
    (Hf: Forall P_f (subfmla_t t))
    (Hp: Forall P_p (subpat_t t)),
    P_subtm t) /\
  (forall (Ht: Forall P_t (subterms_f f))
    (Hf: Forall P_f (subfmla_f f))
    (Hp: Forall P_p (subpat_f f)),
    P_subfmla f).
Proof.
  revert t f; apply term_formula_ind; simpl; intros;
  simpl_forall; split; auto; simpl_forall.
  (*Much easier to automate*)
  - simpl_forall.
    repeat (apply Forall_apply in H; auto).
  - split; simpl_forall; auto.
    apply Forall_and.
    + revert H5. apply Forall_impl. intros. simpl_forall.
      apply P_sub_pat_equiv2; auto.
    + do 3(apply Forall_apply in H0; auto); auto.
      revert H5. apply Forall_impl. intros. simpl_forall; auto.
  - simpl_forall.
    repeat (apply Forall_apply in H; auto).
  - split; simpl_forall; auto.
    apply Forall_and.
    + revert H5. apply Forall_impl. intros. simpl_forall.
      apply P_sub_pat_equiv2; auto.
    + do 3(apply Forall_apply in H0; auto); auto.
      revert H5. apply Forall_impl. intros. simpl_forall; auto.
Qed.

(*And the corollaries*)
Lemma P_subterms_equiv t:
  P_subtm t <-> 
  Forall P_t (subterms_t t) /\
  Forall P_f (subfmla_t t) /\ 
  Forall P_p (subpat_t t).
Proof.
  split.
  - apply (proj_tm P_sub_equiv1 t).
  - intros [Ht [Hf Hp]]. apply (proj_tm P_sub_equiv2 t); auto.
Qed.

Lemma P_subfmlas_equiv f:
  P_subfmla f <-> 
  Forall P_t (subterms_f f) /\
  Forall P_f (subfmla_f f) /\ 
  Forall P_p (subpat_f f).
Proof.
  split.
  - apply (proj_fmla P_sub_equiv1 f).
  - intros [Ht [Hf Hp]]. apply (proj_fmla P_sub_equiv2 f); auto.
Qed.

(*All variables free in subterms or subformulas
  are free or bound in original term*)
(*Subterm formulation makes it easier to reason about
  free variables*)

Ltac simpl_in :=
  repeat(match goal with
  | H: In ?x (concat ?l) |- _ => rewrite in_concat in H
  | H: In ?x (map ?f ?l) |- _ => rewrite in_map_iff in H
  | H: In ?x ?l |- In (?f ?x) (map ?f ?l) => rewrite in_map_iff;
    exists x; auto
  end; destruct_all; subst); try rewrite -> !in_app_iff in *.

Ltac auto_hyp :=
  repeat match goal with
  | H: ?P -> ?Q, H1 : ?P |- _ => specialize (H H1)
  end; auto.

Lemma subterm_fv_in x tm t f:
  (In tm (subterms_t t) -> 
    In x (tm_fv tm) -> In x (tm_fv t) \/
    In x (tm_bnd t)) /\
  (In tm (subterms_f f) -> 
  In x (tm_fv tm) -> In x (fmla_fv f) \/
  In x (fmla_bnd f)).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; 
  destruct_all; try contradiction; simpl in *;
  destruct_all; try contradiction; subst; auto.
  - simpl_in. simpl_set. rewrite in_concat.
    rewrite Forall_forall in H. specialize (H _ H3 H2 H1).
    destruct H; [left | right]; [exists x1 | exists (tm_bnd x1) ]; split; auto.
    simpl_in.
  - simpl_set. simpl_in. vsym_eq x v. 
    repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set.
    repeat (destruct_all; auto_hyp).
  - simpl_set. simpl_in.
    rewrite in_concat.
    destruct H1; [auto_hyp; destruct_all; auto_hyp| simpl_in].
    simpl_forall. rewrite Forall_forall in H0.
    specialize (H0 _ H4).
    destruct (in_dec vsymbol_eq_dec x (pat_fv x1.1)).
    + right. right. eexists. rewrite in_map_iff.
      split. eexists. split;[reflexivity |]. apply H4.
      simpl_in; auto.
    + repeat (destruct_all; auto_hyp); [left | right]; right.
      * exists x1. split; auto. simpl_set. auto.
      * eexists. split. rewrite in_map_iff.
        eexists. split;[reflexivity |]. apply H4.
        simpl_in; auto.
  - simpl_set. vsym_eq x v. repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set. rewrite in_concat.
    rewrite Forall_forall in H. specialize (H _ H3 H2 H1).
    destruct H; [left | right]; [exists x1 | exists (tm_bnd x1) ]; split; auto.
    simpl_in.
  - simpl_in. simpl_set. repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set. repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set. vsym_eq x v. repeat (destruct_all; auto_hyp).
  - simpl_in. simpl_set. repeat (destruct_all; auto_hyp).
  - simpl_set. simpl_in.
    rewrite in_concat.
    destruct H1; [auto_hyp; destruct_all; auto_hyp| simpl_in].
    simpl_forall. rewrite Forall_forall in H0.
    specialize (H0 _ H4).
    destruct (in_dec vsymbol_eq_dec x (pat_fv x1.1)).
    + right. right. eexists. rewrite in_map_iff.
      split. eexists. split;[reflexivity |]. apply H4.
      simpl_in; auto.
    + repeat (destruct_all; auto_hyp); [left | right]; right.
      * exists x1. split; auto. simpl_set. auto.
      * eexists. split. rewrite in_map_iff.
        eexists. split;[reflexivity |]. apply H4.
        simpl_in; auto.
Qed.

(*TODO: reflection?*)
End RecHolds.

Definition tm_wf_strong t :=
  NoDup (map fst (tm_fv t)) /\
  (*TODO: do we need?*)
  NoDup (map fst (tm_bnd t)) /\
  forall x, ~ (In x (map fst (tm_fv t))
  /\ In x (map fst (tm_bnd t))).

Definition fmla_wf_strong f :=
  NoDup (map fst (fmla_fv f)) /\
  NoDup (map fst (fmla_bnd f)) /\
  forall x, ~ (In x (map fst (fmla_fv f)) /\
    In x (map fst (fmla_bnd f))).

Definition tm_wf_strong_rec := P_subtm
  (fun _ => True) tm_wf_strong fmla_wf_strong.

Definition fmla_wf_strong_rec := P_subfmla
(fun _ => True) tm_wf_strong fmla_wf_strong.

(*Plan
  1. Prove if Nodup names of bnd, then NoDup names of bnd for all subterms/fmlas
  2. Prove that all bnd in subterms/fmlas are in t
  3. Use the above (plus fv lemma) to show that
    no overlap in subterms (or else overlap in t)
  4. Prove that if strong condition holds, no free variable dups in any
    subterm
  5. put together (no induction)
  *)

(*Want to show: if we have a term satisfying this condition,
  then it satisfies it recursively*)
  (*
Lemma wf_strong_rec_holds t f:
  (forall (Hwf: tm_wf_strong t), tm_wf_strong_rec t) /\
  (forall (Hwf: fmla_wf_strong f), fmla_wf_strong_rec f).
Proof.
  unfold tm_wf_strong_rec, fmla_wf_strong_rec.
  rewrite -> P_subterms_equiv, P_subfmlas_equiv. split.
  - intros. split_all; auto. 3: rewrite Forall_forall; auto.
    + unfold tm_wf_strong in *.
      destruct_all.

  
  split; intros. unfold tm_wf_strong;
  revert t f. unfold tm_wf_strong_rec, fmla_wf_strong_rec. 
  apply term_formula_ind; simpl; intros.
  - cbn. split; auto.
  - cbn. split; auto.
  - cbn. split; auto.
    simpl_forall.
    revert H. apply Forall_impl_in.
    intros. apply H0.
    clear -Hwf H.
    unfold tm_wf_strong in *.
    simpl in *. split_all.
    + induction l1; simpl in *; try contradiction.
      destruct H; subst.
      * erewrite -> map_union  with(eq_dec2:=string_dec) in H0.


    
    rewrite Forall_forall; intros.
    
    simpl.

*)

(*Now prove that if a term has no duplicate bound variable
  names and is closed, then *)



(*TODO: do NOT generalize ty2*)
(*The above works because v is bound and x is free, so
  name cannot overlap*)
Lemma ty_subst_tf_rep {pd: pi_dom} {pf: pi_funpred gamma_valid pd}
  (t: term) (f: formula):
  (forall (vt: val_typevar) (vv1: val_vars pd vt)
    (vv2: val_vars pd (vt_with_args vt params (map (v_subst vt) tys)))
    (ty1 ty2: vty)
    (Hty1: term_has_type gamma t ty1)
    (Hty2: term_has_type gamma (ty_subst_tm t) ty2)
    (Hvv: forall x Heq, vv2 x = dom_cast (dom_aux pd) Heq 
      (vv1 (ty_subst_var x)))
    Heq,
    (*[term_rep] version is ugly because of cast, but we mostly
      need formula version (or maybe not, see)*)
    term_rep gamma_valid pd vt pf vv1 (ty_subst_tm t) ty2 Hty2 =
    dom_cast (dom_aux pd) Heq (term_rep gamma_valid pd 
      (vt_with_args vt params (map (v_subst vt) tys)) pf
      vv2
      t ty1 Hty1)) /\
  (forall (vt: val_typevar) (vv1: val_vars pd vt) 
  (vv2: val_vars pd (vt_with_args vt params (map (v_subst vt) tys)))
    (Hty1: formula_typed gamma f)
    (Hty2: formula_typed gamma (ty_subst_fmla f))
    (Hvv: forall x Heq, vv2 x = dom_cast (dom_aux pd) Heq 
      (vv1 (ty_subst_var x))),
    (*[term_rep] version is ugly because of cast, but we mostly
      need formula version (or maybe not, see)*)
    formula_rep gamma_valid pd vt pf vv1 (ty_subst_fmla f) Hty2 =
    formula_rep gamma_valid pd 
      (vt_with_args vt params (map (v_subst vt) tys)) pf
      vv2
      f Hty1).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; simpl_rep_full; auto.
  - destruct c; inversion Hty1; inversion Hty2; subst; simpl_rep_full;
    unfold cast_dom_vty.
    + generalize dependent ((Logic.eq_sym (ty_constint_inv Hty1))); intros.
      assert (e = Logic.eq_refl). apply UIP_dec. apply vty_eq_dec.
      subst. simpl. unfold dom_cast; simpl.
      generalize dependent (Logic.eq_sym (ty_constint_inv Hty2)); intros.
      assert (e = Logic.eq_refl). apply UIP_dec. apply vty_eq_dec.
      subst. simpl.
      assert ((f_equal (domain (dom_aux pd)) Heq) = Logic.eq_refl). {
        (*NOTE: relies on UIP*)
        apply UIP.
      }
      rewrite H. reflexivity.
    + generalize dependent ((Logic.eq_sym (ty_constreal_inv Hty1))); intros.
      assert (e = Logic.eq_refl). apply UIP_dec. apply vty_eq_dec.
      subst. simpl. unfold dom_cast; simpl.
      generalize dependent (Logic.eq_sym (ty_constreal_inv Hty2)); intros.
      assert (e = Logic.eq_refl). apply UIP_dec. apply vty_eq_dec.
      subst. simpl.
      assert ((f_equal (domain (dom_aux pd)) Heq) = Logic.eq_refl). {
        (*NOTE: relies on UIP*)
        apply UIP.
      }
      rewrite H. reflexivity.
  - (*Variable case - more casting*)
    unfold var_to_dom.
    inversion Hty1; inversion Hty2; subst.
    rewrite Hvv. auto. intros.
    rewrite !dom_cast_compose.
    (*If we do not use upd_vv_args'', this is not provable*)
    apply dom_cast_eq.
  - (*Function case - hard because of casting already and
    need nested inductive lemma for get_arg_list*)
    unfold cast_dom_vty. rewrite !dom_cast_compose.
    assert (Hmap: (map (v_subst vt) (ty_subst_list' params tys l)) =
    (map (v_subst (vt_with_args vt params (map (v_subst vt) tys))) l)). {
      apply list_eq_ext'; rewrite !map_length; auto.
      intros n d Hn. unfold ty_subst_list'.
      rewrite !map_map.
      rewrite -> !map_nth_inbound with (d2:=vty_int); auto.
      apply v_subst_vt_with_args'.
    }
    match goal with
    | |- dom_cast ?d ?H ?x = dom_cast ?d ?H1 ?x1 =>
      generalize dependent H; 
      generalize dependent H1
    end.
    
    assert (Hargs:
    cast_arg_list (f_equal (sym_sigma_args f1) Hmap)
    (fun_arg_list pd vt f1 (ty_subst_list' params tys l) (map ty_subst_tm l1)
    (term_rep gamma_valid pd vt pf vv1) Hty2) =
    (fun_arg_list pd (vt_with_args vt params (map (v_subst vt) tys)) f1 l l1
        (term_rep gamma_valid pd (vt_with_args vt params (map (v_subst vt) tys)) pf
           vv2) Hty1)).
    {
      unfold fun_arg_list.
      apply (get_arg_list_vt_ext') with(s:=f1)(Heq:=Hmap);
      rewrite map_length; auto.
      revert H; rewrite Forall_forall; intros.
      revert Hty0. rewrite -> map_nth_inbound with (d2:=tm_d); auto.
      intros.
      erewrite H; [|apply nth_In; auto |].
      rewrite !dom_cast_compose. apply dom_cast_refl.
      intros. apply Hvv.
      Unshelve.
      auto.
    }
    rewrite <- Hargs.
    intros.
    rewrite <- funs_cast_eq.
    rewrite !dom_cast_compose. apply dom_cast_eq.
  - (*Tlet case*)
    assert (Heq1: v_subst (vt_with_args vt params (map (v_subst vt) tys)) v.2 =
    v_subst vt (ty_subst' params tys v.2)).
    {
      symmetry; apply v_subst_vt_with_args'.
    }
    erewrite -> H with(vv2:=vv2)(ty1:=snd v)(Heq:=Heq1)(Hty1:=(proj1' (ty_let_inv Hty1))).
    assert (Heq2: v_subst (vt_with_args vt params (map (v_subst vt) tys)) ty1 = v_subst vt ty2).
    {
      inversion Hty1; subst; inversion Hty2; subst.
      (*Use typing*)
      assert (ty2 = ty_subst' params tys ty1). {
        (*TODO: import typechecker*)
        eapply term_has_type_unique. apply H9.
        apply ty_subst_t_ty; auto.
        (*TODO: require*) admit.
      }
      subst. rewrite v_subst_vt_with_args'; auto.
    }
    2: { intros; apply Hvv. }
    apply H0.
    intros. unfold substi.
    vsym 
    
    with(ty1:=ty1)(Hty1:=(proj2' (ty_let_inv Hty1)))(Heq:=Heq2).
    (*Now we show that the inner is the same*)
    erewrite tm_change_vv.
    apply dom_cast_eq.
    intros. 
    (*TODO: how substi interacts with [upd_vv_args'']*)


    Unshelve.


    apply H0.
    Unshelve.
  assert (Heq1: v_subst vt2 (snd v) = v_subst vt1 (snd v)). {
    eapply (@vv_cast_tm2 (Tlet tm1 v tm2) _ _ vv2 vv1); simpl; auto.
    intros; symmetry; apply Hvt; auto.
  }
  rewrite H with (vv2:=vv2)(Heq:=Heq1); intros;
  [| apply Hvt | apply Hvv]; simpl; simpl_set; auto.
  (*Now the outer term_rep*)
  apply H0; intros; [apply Hvt |]; simpl; simpl_set; auto.
  (*Now have to show vv condition*)
  unfold substi. destruct (vsymbol_eq_dec x v); subst; simpl.
  + unfold eq_rec_r, eq_rec, eq_rect. simpl.
    rewrite !dom_cast_compose.
    rewrite dom_cast_refl. reflexivity.
  + apply Hvv. simpl; simpl_set; auto. *)



(*TODO: 
  X push this fv stuff through terms and fmlas
  X Prove typing for terms and formulas
  Prove rep for patterns
  Prove rep for terms and formulas
  monomoprhic goal (maybe with )
  Test case?
  
  Then unfolding*)


  simpl.



      apply (H11 i j Pwild x0 H0 H1 H2); split; auto. 



  ty_subst_twice

  
  Check P_Constr.
  
  
  constructor.
  
  

  induction p.

  
    | _ => t
  end.


Print ty_subst.
Print ty_subst_list.


(*Produce proof goals for lemmas and goals*)
Fixpoint valid_theory (t: theory) : Prop :=
  match t with
  | nil => True
  | (tprop k _ f :: tl) =>
    match k with 
    | Paxiom => (*we only require that the task is wf, not
      valid*) task_wf (mk_task (theory_ctx_int tl) 
        (theory_axioms_int tl) f) 
      /\ valid_theory tl
    | _ =>
      task_valid (mk_task (theory_ctx_int tl)
        (theory_axioms_int tl) f) /\
      valid_theory tl
    end
  | _ :: tl => valid_theory tl
  end.

(*An alternate approach that is more efficient and 
  (hopefully) avoids some opaque issues*)



(*Inductive valid_theory : theory -> Prop :=
  | valid_th_emp: valid_theory nil
  | valid_th_def: forall d t,
    valid_theory t ->
    (*(*The context with this def is well-typed*)
    valid_context (d :: theory_ctx_int t) ->*)
    valid_theory (tdef d :: t)
  (*For axioms, only need to check type I think*)
  | valid_th_axiom: forall name f t,
    valid_theory t ->
    formula_typed (theory_ctx_int t) f ->
    valid_theory (tprop Paxiom name f :: t)
  | valid_th_lemma: forall name f t,
    valid_theory t ->
    (*We build the task consisting of the context
      of the theory, the assumptions so far, and the 
      goal*)
    task_valid (mk_task (theory_ctx_int t)
    (map snd (theory_axioms_int t)) nil f) ->
    valid_theory (tprop Plemma name f :: t)
  (*goals are identical*)
  | valid_th_goal: forall name f t,
    valid_theory t ->
    (*We build the task consisting of the context
      of the theory, the assumptions so far, and the 
      goal*)
    task_valid (mk_task (theory_ctx_int t)
      (map snd (theory_axioms_int t)) nil f) ->
    valid_theory (tprop Pgoal name f :: t)
  (*For "use", just need existing theory to be valid*)
  | valid_th_use: forall th b t,
    valid_theory t ->
    valid_theory th ->
    valid_theory (tuse th b :: t)
  (*And similarly for clone, but we need to ensure that
    the things that we substitute are valid (TODO: in typing?)*)
  | valid_th_clone: forall th name tys funs preds t,
    valid_theory t ->
    valid_theory th ->
    let gamma := theory_ctx_int t in
    (forall ty, In ty (map snd tys) -> In ty (sig_t gamma)) ->
    (forall f, In f (map snd funs) -> In f (sig_f gamma)) ->
    (forall p, In p (map snd preds) -> In p (sig_p gamma)) ->
    valid_theory (tclone th name tys funs preds :: t).

    (*
    Require Import Typechecker.
(*Here, we will build a list of props that together imply
  that the theory is well-typed and valid (which we prove).
  All are decidable and can thus be solved by "reflexivity"
  except for the [task_valid] ones*)
(*TODO: maybe combine, for now only valid*)
Fixpoint get_theory_tasks (t: theory) : list Prop :=
  match t with
  | nil => True
  | tdecl d :: tl => get_theory_tasks tl
  | 


  valid_th_axiom: forall name f t,
    valid_theory t ->
    formula_typed (theory_ctx_int t) f ->
    valid_theory (tprop Paxiom name f :: t)
    (*TODO: inefficient to get entire context here*)


*)*)