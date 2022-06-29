Require Import Types.
Require Export Coq.Reals.Reals.

(** Function and Predicate Symbols **)

Record funsym :=
  {
    s_name : string;
    s_params : list typevar;
    s_args: list vty;
    s_ret: vty;
    (*Well-formed - all type variables appear in params*)
    s_ret_wf: sublist (type_vars s_ret) s_params;
    s_args_wf: forall x, In x s_args -> sublist (type_vars x) s_params
  }.

Record predsym :=
  {
    p_name: string;
    p_params: list typevar;
    p_args : list vty;
    p_args_wf: forall x, In x p_args -> sublist (type_vars x) p_params
  }.

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
Defined.

(*As an example, we define the polymorphic identity function*)
Section ID.

Definition id_name : string := "id".
Definition a : string := "a".
Definition id_params : list typevar := [a].
Definition id_args: list vty := [vty_var a].
Definition id_ret: vty := vty_var a.

Definition id_fs : funsym.
apply (mk_funsym id_name id_params id_args id_ret); reflexivity.
Defined.

End ID.

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
  | Pvar : string -> vty -> pattern
  | Pconstr : funsym -> list vty -> list pattern -> pattern
  | Pwild : pattern
  | Por: pattern -> pattern -> pattern
  | Pbind: pattern -> string -> vty -> pattern.

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

(*Free variables of a pattern*)
Fixpoint pat_fv (p: pattern) : list vsymbol :=
  match p with
  | Pvar x t => [x]
  | Pwild => []
  | Pconstr _ _ ps => big_union vsymbol_eq_dec pat_fv ps
  | Por p1 p2 => union vsymbol_eq_dec (pat_fv p1) (pat_fv p2)
  | Pbind p x t => union vsymbol_eq_dec (pat_fv p) [x]
  end.

(*Definitions: functions, predicates, algebraic data types, inductive predicates*)

Inductive alg_datatype : Type :=
  | alg_def: typesym -> list funsym -> alg_datatype.

Inductive funpred_def : Type :=
  | fun_def: funsym -> term -> funpred_def
  | pred_def: predsym -> formula -> funpred_def.

(*TODO: more restrictive than formula - we can either define a predicate that
  it is valid, or we can define another inductive type *)
Inductive indpred_def : Type :=
  | ind_def: predsym -> list formula -> indpred_def.

Inductive def : Type :=
  | datatype_def : list alg_datatype -> def (*for mutual recursion*)
  | recursive_def: list funpred_def -> def
  | inductive_def : list indpred_def -> def.
