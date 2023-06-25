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

(*And now, finally, we can deal with polymorphism*)

(*TODO: 
  X push this fv stuff through terms and fmlas
  X Prove typing for terms and formulas
  Prove rep for patterns
  Prove rep for terms and formulas
  monomoprhic goal (maybe with )
  Test case?
  
  Then unfolding*)

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