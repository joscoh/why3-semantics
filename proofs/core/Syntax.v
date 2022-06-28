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

(*As an example, we define the polymorphic identity function*)
Section ID.

Definition id_name : string := "id".
Definition a : string := "a".
Definition id_params : list typevar := [a].
Definition id_args: list vty := [vty_var a].
Definition id_ret: vty := vty_var a.
Lemma id_ret_wf: sublist (type_vars id_ret) id_params.
Proof.
  simpl. unfold id_params, sublist. auto.
Qed.
Lemma id_args_wf: forall x, In x id_args -> sublist (type_vars x) id_params.
Proof.
  intros x. simpl. intros [Hx| []]; subst. simpl. unfold id_params, sublist.
  auto.
Qed. 
Definition idsym := Build_funsym id_name id_params id_args id_ret id_ret_wf id_args_wf.

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

Unset Elimination Schemes.
(*No case/match at the moment*)
Inductive term : Type :=
  | Tconst: constant -> term
  | Tvar : nat -> vty -> term
  | Tfun: funsym -> list vty -> list term -> term
  | Tlet: term -> vty -> term -> term
  | Tif: formula -> term -> term -> term
with formula : Type :=
  | Fpred: predsym -> list vty -> list term -> formula
  | Fquant: quant -> vty -> formula -> formula
  | Feq: vty -> term -> term -> formula
  | Fbinop: binop -> formula -> formula -> formula
  | Fnot: formula -> formula
  | Ftrue: formula
  | Ffalse: formula
  | Flet: term -> vty -> formula -> formula
  | Fif: formula -> formula -> formula -> formula.
  (*TODO: will need nicer (useful) induction scheme*)
  Set Elimination Schemes.

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

