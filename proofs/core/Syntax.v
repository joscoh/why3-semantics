Require Import Types.
Require Export Coq.Reals.Reals.

(** Function and Predicate Symbols **)

(*We use bools rather than props so that we get decidable equality (like ssreflect)*)

(*Check for sublist (to enable building these structures)*)
Definition check_sublist (l1 l2: list typevar) : bool :=
  forallb (fun x => in_dec typevar_eq_dec x l2) l1.

Lemma check_sublist_correct: forall l1 l2,
  reflect (sublist l1 l2) (check_sublist l1 l2).
Proof.
  intros. destruct (check_sublist l1 l2) eqn : Hsub.
  - unfold check_sublist in Hsub. rewrite forallb_forall in Hsub.
    apply ReflectT. unfold sublist; intros.
    apply Hsub in H. simpl_sumbool.
  - apply ReflectF. unfold sublist. intro.
    assert (check_sublist l1 l2 = true). {
      apply forallb_forall. intros. simpl_sumbool.
    }
    rewrite H0 in Hsub; inversion Hsub.
Qed.

Definition check_args (params: list typevar) (args: list vty) : bool :=
  forallb (fun x => check_sublist (type_vars x) params) args.

(*Would be easier with ssreflect*)
Lemma check_args_correct: forall params args,
  reflect (forall x, In x args -> sublist (type_vars x) params) (check_args params args).
Proof.
  intros. destruct (check_args params args) eqn : Hargs.
  - unfold check_args in Hargs. rewrite forallb_forall in Hargs.
    apply ReflectT. intros. apply Hargs in H.
    apply (reflect_iff _  _ (check_sublist_correct (type_vars x) params)) in H. auto.
  - apply ReflectF. intro C.
    assert (check_args params args = true). {
      apply forallb_forall. intros. apply C in H.
      apply (reflect_iff _ _ (check_sublist_correct (type_vars x) params)). auto.
    }
    rewrite H in Hargs; inversion Hargs.
Qed.

(*Easy corollaries, need these for arguments to other functions which don't know
  about the decidable versions*)

Lemma check_args_prop {params args} :
  check_args params args -> forall x, In x args -> sublist (type_vars x) params.
Proof.
  intros Hcheck. apply (reflect_iff _ _ (check_args_correct params args)).
  apply Hcheck.
Qed.

Lemma check_sublist_prop {l1 l2}:
  check_sublist l1 l2 ->
  sublist l1 l2.
Proof.
  intros. apply (reflect_iff _ _ (check_sublist_correct l1 l2)), H.
Qed.

Record funsym :=
  {
    s_name : string;
    s_params : list typevar;
    s_args: list vty;
    s_ret: vty;
    (*Well-formed - all type variables appear in params*)
    s_ret_wf: check_sublist (type_vars s_ret) s_params;
    s_args_wf: check_args s_params s_args
  }.

Record predsym :=
  {
    p_name: string;
    p_params: list typevar;
    p_args : list vty;
    p_args_wf: check_args p_params p_args
  }.

(*
Definition mk_funsym (name: string) (params : list typevar) (args: list vty)
  (ret: vty) : (check_args params args = true) ->
    (check_sublist (type_vars ret) params = true) -> funsym.
Proof.
  intros. econstructor.
  apply name.
  apply (reflect_iff _ _ (check_sublist_correct (type_vars ret) params)). assumption.
  apply (reflect_iff _ _ (check_args_correct params args)). assumption.
Defined.

Definition mk_predsym (name: string) (params: list typevar) (args: list vty) :
  (check_args params args = true) -> predsym.
Proof.
  intros. econstructor.
  apply name. apply (reflect_iff _ _ (check_args_correct params args)). assumption.
Defined.*)

(*As an example, we define the polymorphic identity function*)
Section ID.

Definition id_name : string := "id".
Definition a : string := "a".
Definition id_params : list typevar := [a].
Definition id_args: list vty := [vty_var a].
Definition id_ret: vty := vty_var a.

Definition id_fs : funsym := Build_funsym id_name id_params id_args id_ret eq_refl eq_refl.

End ID.

Section SymEqDec.

Ltac dec H :=
  destruct H; [subst | right; let C := fresh in intro C; inversion C; auto].

(*Decidable equality on funsyms/predsyms (why we use booleans)*)
Lemma funsym_eq_dec: forall (f1 f2: funsym), {f1 = f2} + {f1 <> f2}.
Proof.
  intros. destruct f1; destruct f2; simpl.
  dec (string_dec s_name0 s_name1).
  dec (list_eq_dec typevar_eq_dec s_params0 s_params1).
  dec (list_eq_dec vty_eq_dec s_args0 s_args1).
  dec (vty_eq_dec s_ret0 s_ret1).
  assert (s_ret_wf0 = s_ret_wf1) by apply bool_irrelevance; subst.
  assert (s_args_wf0 = s_args_wf1) by apply bool_irrelevance; subst.
  left; reflexivity.
Defined.

Lemma predsym_eq_dec: forall (p1 p2: predsym), {p1 = p2} + {p1 <> p2}.
Proof.
  intros; destruct p1; destruct p2.
  dec (string_dec p_name0 p_name1).
  dec (list_eq_dec typevar_eq_dec p_params0 p_params1).
  dec (list_eq_dec vty_eq_dec p_args0 p_args1).
  assert (p_args_wf0 = p_args_wf1) by apply bool_irrelevance; subst.
  left; reflexivity.
Defined.

End SymEqDec.

(** Syntax - Terms and Formulas **)

Inductive constant : Type :=
  | ConstInt : Z -> constant
  | ConstReal : R -> constant
  | ConstStr : string -> constant.

Inductive quant : Type :=
    | Tforall
    | Texists.

Inductive binop : Type :=
    | Tand
    | Tor
    | Timplies
    | Tiff.

Definition vsymbol := string.

Definition vsymbol_eq_dec : forall (x y: vsymbol), {x = y} + {x <> y} := string_dec.

Unset Elimination Schemes.
Inductive pattern : Type :=
  | Pvar : vsymbol -> vty -> pattern
  | Pconstr : funsym -> list vty -> list pattern -> pattern
  | Pwild : pattern
  | Por: pattern -> pattern -> pattern
  | Pbind: pattern -> vsymbol -> vty -> pattern.

(*No case/match at the moment*)
Inductive term : Type :=
  | Tconst: constant -> term
  | Tvar : vsymbol -> vty -> term
  | Tfun: funsym -> list vty -> list term -> term
  | Tlet: term -> vsymbol -> vty -> term -> term
  | Tif: formula -> term -> term -> term
  | Tmatch: term -> list (pattern * term) -> term
with formula : Type :=
  | Fpred: predsym -> list vty -> list term -> formula
  | Fquant: quant -> vsymbol -> vty -> formula -> formula
  | Feq: vty -> term -> term -> formula
  | Fbinop: binop -> formula -> formula -> formula
  | Fnot: formula -> formula
  | Ftrue: formula
  | Ffalse: formula
  | Flet: term -> vsymbol -> vty -> formula -> formula
  | Fif: formula -> formula -> formula -> formula
  | Fmatch: term -> list (pattern * formula) -> formula.
  (*TODO: will need nicer (useful) induction scheme*)
Set Elimination Schemes.

Scheme term_ind := Induction for term Sort Prop
with formula_ind := Induction for formula Sort Prop.

(*Induction principles*)
Section PatternInd.

Variable P: pattern -> Prop.
Variable Hvar: forall (v: vsymbol) (ty: vty),
  P (Pvar v ty).
Variable Hconstr: forall (f: funsym) (vs: list vty) (ps: list pattern),
  Forall P ps ->
  P (Pconstr f vs ps).
Variable Hwild: P Pwild.
Variable Hor: forall p1 p2, P p1 -> P p2 -> P (Por p1 p2).
Variable Hbind: forall p v ty,
  P p -> P (Pbind p v ty).

Fixpoint pattern_ind (p: pattern) : P p :=
  match p with
  | Pvar x ty => Hvar x ty
  | Pconstr f tys ps => Hconstr f tys ps
    ((fix all_patterns (l: list pattern) : Forall P l :=
    match l with
    | nil => @Forall_nil _ P
    | x :: t => @Forall_cons _ P _ _ (pattern_ind x) (all_patterns t)
    end) ps)
  | Pwild => Hwild
  | Por p1 p2 => Hor p1 p2 (pattern_ind p1) (pattern_ind p2)
  | Pbind p x ty => Hbind p x ty (pattern_ind p)
  end.

End PatternInd.

Section FreeVars.

Local Notation union' := (union vsymbol_eq_dec).
Local Notation big_union' := (big_union vsymbol_eq_dec).
Local Notation remove' := (remove vsymbol_eq_dec).
Local Notation remove_all' := (remove_all vsymbol_eq_dec).

(*Free variables of a pattern*)
Fixpoint pat_fv (p: pattern) : list vsymbol :=
  match p with
  | Pvar x t => [x]
  | Pwild => []
  | Pconstr _ _ ps => big_union' pat_fv ps
  | Por p1 p2 => union' (pat_fv p1) (pat_fv p2)
  | Pbind p x t => union' (pat_fv p) [x]
  end.

(*Free variables of a term (all variables that appear free at least once)*)
Fixpoint term_fv (t: term) : list vsymbol :=
  match t with
  | Tconst _ => nil
  | Tvar x _ => [x]
  | Tfun f vtys tms => big_union' term_fv tms
  | Tlet t1 v _ t2 => union' (term_fv t1) (remove' v (term_fv t2))
  | Tif f t1 t2 => union' (form_fv f) (union' (term_fv t1) (term_fv t2))
  | Tmatch t l => union' (term_fv t) (big_union' (fun x => remove_all' (pat_fv (fst x)) (term_fv (snd x))) l)
  end

with form_fv (f: formula) : list vsymbol :=
  match f with
  | Fpred p tys tms => big_union' term_fv tms
  | Fquant q v _ f => remove' v (form_fv f)
  | Feq _ t1 t2 => union' (term_fv t1) (term_fv t2)
  | Fbinop b f1 f2 => union' (form_fv f1) (form_fv f2)
  | Fnot f => form_fv f
  | Ftrue => nil
  | Ffalse => nil
  | Flet t v _ f => union' (term_fv t) (remove' v (form_fv f))
  | Fif f1 f2 f3 => union' (form_fv f1) (union' (form_fv f2) (form_fv f3))
  | Fmatch t l => union' (term_fv t) (big_union' (fun x => remove_all' (pat_fv (fst x)) (form_fv (snd x))) l)
  end.

Definition closed_term (t: term) : bool :=
  null (term_fv t).
Definition closed_formula (f: formula) : bool :=
  null (form_fv f).

End FreeVars.

(*Definitions: functions, predicates, algebraic data types, inductive predicates*)

Inductive alg_datatype : Type :=
  | alg_def: typesym -> list funsym -> alg_datatype.

Inductive funpred_def : Type :=
  | fun_def: funsym -> list vsymbol -> term -> funpred_def
  | pred_def: predsym -> list vsymbol -> formula -> funpred_def.

(*TODO: more restrictive than formula - we can either define a predicate that
  it is valid, or we can define another inductive type *)
Inductive indpred_def : Type :=
  | ind_def: predsym -> list formula -> indpred_def.

Inductive def : Type :=
  | datatype_def : list alg_datatype -> def (*for mutual recursion*)
  | recursive_def: list funpred_def -> def
  | inductive_def : list indpred_def -> def.

Definition datatypes_of_def (d: def) : list (typesym * list funsym) :=
  match d with
  | datatype_def la => map (fun a =>
      match a with
      | alg_def ts fs => (ts, fs)
      end) la
  | recursive_def _ => nil
  | inductive_def _ => nil
  end.

Definition fundefs_of_def (d: def) : list (funsym * list vsymbol * term) :=
  match d with
  | recursive_def lf =>
    fold_right (fun x acc => match x with
      | fun_def fs vs t => (fs, vs, t) :: acc
      | _ => acc
      end) nil lf
  | _ => nil
  end.

Definition preddefs_of_def (d: def) : list (predsym * list vsymbol * formula) :=
  match d with
  | recursive_def lf =>
    fold_right (fun x acc => match x with
      | pred_def ps vs f => (ps, vs, f) :: acc
      | _ => acc
      end) nil lf
  | _ => nil
  end.

(*TODO: may want function for indprops as well*)

Definition funsyms_of_def (d: def) : list funsym :=
  match d with
  | datatype_def la => concat ((map (fun a =>
    match a with
    | alg_def _ fs => fs
    end)) la)
  | recursive_def lf =>
    fold_right (fun x acc => match x with
      | fun_def fs _ _ => fs :: acc
      | _ => acc
      end) nil lf
  | inductive_def _ => nil
  end.

Definition predsyms_of_def (d: def) : list predsym :=
  match d with
  | datatype_def _ => nil
  | recursive_def lf =>
    fold_right (fun x acc => match x with
    | pred_def ps _ _ => ps :: acc
    | _ => acc
    end) nil lf
  | inductive_def is => map (fun a =>
    match a with
    | ind_def ps _ => ps
    end) is
  end.