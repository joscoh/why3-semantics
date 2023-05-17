Require Export FullInterp.
(*Why3 Theories*)


(*We depart from Why3 notation slightly here, since we make a distinction
  between a context (with declarations) and a theory
  environment, which contains lemmas, axioms, goals, and 
  use/clone of another theory*)

(*Syntax*)
Print vty.
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
(*Induction principle not good for this one*)
Inductive tdecl : Set :=
  | tdef : def -> tdecl
  | tprop : prop_kind -> string -> formula -> tdecl
  (*Use a theory (copy all of its definitions).
    Bool represents if exported or not*)
  | tuse : list tdecl -> bool -> tdecl
  (*Clone a theory - instantiating some parameters and giving
    a qualified name*)
  | tclone: list tdecl -> string -> list (typesym * typesym) ->
    list (funsym * funsym) -> list (predsym * predsym) -> bool -> tdecl.

Definition theory : Set := list tdecl.

(*To write inductive functions over theories that
  recurse as we expect (into tuse and tclone), we define a 
  notion of "size"*)
Fixpoint tdecl_size (t: tdecl) : nat :=
  match t with
  | tdef d => 1
  | tprop _ _ _ => 1
  | tuse ts _ => 1 + sum (map tdecl_size ts)
  | tclone ts _ _ _ _ _ => 1 + sum (map tdecl_size ts)
  end.

Definition theory_size (t: theory) : nat :=
  sum (map tdecl_size t).

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
  and the external one, which only includes "use"s and "clone"s
  marked as exported
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
Print term.

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
  | Tvar v => Tvar v
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

End Sub.

Print tdecl.

(*The external context of a theory*)

(*TODO: need to implement qualified names*)

#[local] Instance theory_size_wf:
Classes.WellFounded
        (Telescopes.tele_measure (Telescopes.tip theory) nat
           (fun t : theory => theory_size t) lt).
unfold Classes.WellFounded, Telescopes.tele_measure. simpl.
apply Inverse_Image.wf_inverse_image.
apply Nat.lt_wf_0.
Defined.

(*Solves all goals*)
Obligation Tactic := intros; try (unfold theory_size); simpl; try lia.

(*We use Equations because this is not obviously stucturally
  recursive (or at least Coq cannot tell that it is)*)
Equations theory_ctx_ext (t: theory) : context
  by wf (theory_size t) lt :=
theory_ctx_ext (tdef d :: tl) := d :: theory_ctx_ext tl;
theory_ctx_ext (tuse l true :: tl) :=
  (*Not structurally recursive*)
  theory_ctx_ext l ++ theory_ctx_ext tl;
theory_ctx_ext (tclone l _ tys funs preds true :: tl) :=
  sub_ctx_map tys funs preds (theory_ctx_ext l) ++ theory_ctx_ext tl;
theory_ctx_ext (_ :: tl) := theory_ctx_ext tl;
theory_ctx_ext nil := nil.

(*And the internal theory context - only use external context
  of imported modules - this one is structurally recursive*)
Fixpoint theory_ctx_int (t: theory) : context :=
  match t with
  | tdef d :: tl => d :: theory_ctx_int tl
  | tuse l true :: tl =>
      theory_ctx_ext l ++ theory_ctx_int tl
  | tclone l _ tys funs preds _ :: tl =>
    sub_ctx_map tys funs preds (theory_ctx_ext l) ++ theory_ctx_int tl
  | _ :: tl => theory_ctx_int tl
  | nil => nil
  end.

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
