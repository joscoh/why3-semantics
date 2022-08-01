Require Import Types.
Require Import Common.
Require Export Coq.Reals.Reals.

From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

(** Function and Predicate Symbols **)

(*We use bools rather than props so that we get decidable equality (like ssreflect)*)

(*Check for sublist (to enable building these structures)*)
Definition check_sublist (l1 l2: list typevar) : bool :=
  all (fun x => x \in l2) l1.

(*TODO: sublist in terms of mem?*)
Lemma check_sublistP: forall l1 l2,
  reflect (sublist l1 l2) (check_sublist l1 l2).
Proof.
  move=>l1 l2. (*rewrite /check_sublist.*)
  case: (check_sublist l1 l2) /allP => /= Hall.
  - apply ReflectT. rewrite /sublist.
    move=>x /inP Hin. apply /inP. by apply Hall.
  - apply ReflectF. rewrite /sublist => Hin.
    apply Hall. move => x /inP Hinx. apply /inP.
    by apply Hin.
Qed.

Definition check_args (params: list typevar) (args: list vty) : bool :=
  all (fun x => check_sublist (type_vars x) params) args.

Lemma check_argsP: forall params args,
  reflect (forall x, In x args -> sublist (type_vars x) params) (check_args params args).
Proof.
  move=>p a. case:(check_args p a) /allP => /= Hall.
  - apply ReflectT. move => x /inP Hinx.
    by move: Hall => /(_ x Hinx) /check_sublistP.
  - apply ReflectF => Hc.
    apply Hall => x /inP Hinx. apply /check_sublistP.
    by apply Hc.
Qed.

Record funsym :=
  {
    s_name : string;
    s_params : list typevar;
    s_args: list vty;
    s_ret: vty;
    (*Well-formed - all type variables appear in params*)
    s_ret_wf: check_sublist (type_vars s_ret) s_params;
    s_args_wf: check_args s_params s_args;
    s_params_nodup: uniq s_params
  }.

Record predsym :=
  {
    p_name: string;
    p_params: list typevar;
    p_args : list vty;
    p_args_wf: check_args p_params p_args;
    p_params_nodup: uniq p_params
  }.

(*As an example, we define the polymorphic identity function*)
Section ID.

Definition id_name : string := "id".
Definition a : string := "a".
Definition id_params : list typevar := [a].
Definition id_args: list vty := [vty_var a].
Definition id_ret: vty := vty_var a.

Definition id_fs : funsym := Build_funsym id_name id_params id_args id_ret erefl erefl erefl.

End ID.

Section SymEqDec.

Lemma funsym_eq: forall (f1 f2: funsym),
  (s_name f1) = (s_name f2) ->
  (s_params f1) = (s_params f2) ->
  (s_args f1) = (s_args f2) ->
  (s_ret f1) = (s_ret f2) ->
  f1 = f2.
Proof.
  intros. destruct f1; destruct f2; simpl in *; subst.
  assert (s_params_nodup0 = s_params_nodup1) by apply bool_irrelevance; subst.
  assert (s_ret_wf0=s_ret_wf1) by apply bool_irrelevance; subst.
  assert (s_args_wf0=s_args_wf1) by apply bool_irrelevance; subst.
  reflexivity.
Qed.

Ltac dec H :=
  destruct H; [ simpl | apply ReflectF; intro C; inversion C; subst; contradiction].

Definition funsym_eqb (f1 f2: funsym) : bool :=
  (String.eqb (s_name f1) (s_name f2)) &&
  (list_eq_dec typevar_eq_dec (s_params f1) (s_params f2)) &&
  (list_eq_dec vty_eq_dec (s_args f1) (s_args f2)) &&
  (vty_eq_dec (s_ret f1) (s_ret f2)).

Lemma funsym_eqb_spec: forall (f1 f2: funsym),
  reflect (f1 = f2) (funsym_eqb f1 f2).
Proof.
  intros. unfold funsym_eqb.
  dec (String.eqb_spec (s_name f1) (s_name f2)).
  dec (list_eq_dec typevar_eq_dec (s_params f1) (s_params f2)).
  dec (list_eq_dec vty_eq_dec (s_args f1) (s_args f2)).
  dec (vty_eq_dec (s_ret f1) (s_ret f2)).
  apply ReflectT. apply funsym_eq; auto.
Qed.

Definition funsym_eq_dec (f1 f2: funsym) : {f1 = f2} + {f1 <> f2} :=
  reflect_dec' (funsym_eqb_spec f1 f2).

(*We do the same for predicate symbols*)
Lemma predsym_eq: forall (p1 p2: predsym),
  (p_name p1) = (p_name p2) ->
  (p_params p1) = (p_params p2) ->
  (p_args p1) = (p_args p2) ->
  p1 = p2.
Proof.
  intros; destruct p1; destruct p2; simpl in *; subst.
  assert (p_params_nodup0=p_params_nodup1) by apply bool_irrelevance; subst.
  assert (p_args_wf0=p_args_wf1) by apply bool_irrelevance; subst. reflexivity.
Qed.

Definition predsym_eqb (p1 p2: predsym) : bool :=
  (String.eqb (p_name p1) (p_name p2)) &&
  (list_eq_dec typevar_eq_dec (p_params p1) (p_params p2)) &&
  (list_eq_dec vty_eq_dec (p_args p1) (p_args p2)).

Lemma predsym_eqb_spec: forall (p1 p2: predsym),
  reflect (p1 = p2) (predsym_eqb p1 p2).
Proof.
  intros. unfold predsym_eqb.
  dec (String.eqb_spec (p_name p1) (p_name p2)).
  dec (list_eq_dec typevar_eq_dec (p_params p1) (p_params p2)).
  dec (list_eq_dec vty_eq_dec (p_args p1) (p_args p2)).
  apply ReflectT. apply predsym_eq; auto.
Qed.

Definition predsym_eq_dec (p1 p2: predsym) : {p1 = p2} + {p1 <> p2} :=
  reflect_dec' (predsym_eqb_spec p1 p2).

(*We do the same for predicate symbols*)
Lemma predsym_eq: forall (p1 p2: predsym),
  (p_name p1) = (p_name p2) ->
  (p_params p1) = (p_params p2) ->
  (p_args p1) = (p_args p2) ->
  p1 = p2.
Proof.
  intros; destruct p1; destruct p2; simpl in *; subst.
  assert (p_params_nodup0=p_params_nodup1) by apply bool_irrelevance; subst.
  assert (p_args_wf0=p_args_wf1) by apply bool_irrelevance; subst. reflexivity.
Qed.

Definition predsym_eqb (p1 p2: predsym) : bool :=
  ((p_name p1) == (p_name p2)) &&
  ((p_params p1) == (p_params p2)) &&
  ((p_args p1) == (p_args p2)).

Lemma predsym_eqb_axiom: Equality.axiom predsym_eqb.
Proof.
  move=>p1 p2. rewrite /predsym_eqb.
  case_reflect (p_name p1) (p_name p2).
  case_reflect (p_params p1) (p_params p2).
  case_reflect (p_args p1) (p_args p2).
  apply ReflectT. by apply predsym_eq.
Qed.

Definition predsym_eqMixin := EqMixin predsym_eqb_axiom.
Canonical predsym_eqType := EqType predsym predsym_eqMixin.

End SymEqType.

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

Canonical vsymbol_eqType := EqType vsymbol string_eqMixin.

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
  | Tmatch: term -> vty -> list (pattern * term) -> term
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
  | Fmatch: term -> vty -> list (pattern * formula) -> formula.
  (*TODO: will need nicer (useful) induction scheme*)
Set Elimination Schemes.

Scheme term_ind := Induction for term Sort Prop
with formula_ind := Induction for formula Sort Prop.

Scheme term_rec := Induction for term Sort Set
with formula_rec := Induction for formula Sort Set.

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
(*
Local Notation union' := (union vsymbol_eq_dec).
Local Notation big_union' := (big_union vsymbol_eq_dec).
Local Notation remove' := (remove vsymbol_eq_dec).
Local Notation remove_all' := (remove_all vsymbol_eq_dec).
*)
(*Free variables of a pattern*)
Fixpoint pat_fv (p: pattern) : list vsymbol :=
  match p with
  | Pvar x t => [x]
  | Pwild => []
  | Pconstr _ _ ps => big_union pat_fv ps
  | Por p1 p2 => union (pat_fv p1) (pat_fv p2)
  | Pbind p x t => union (pat_fv p) [x]
  end.

(*Free variables of a term (all variables that appear free at least once)*)
Fixpoint term_fv (t: term) : list vsymbol :=
  match t with
  | Tconst _ => nil
  | Tvar x _ => [x]
  | Tfun f vtys tms => big_union term_fv tms
  | Tlet t1 v _ t2 => union (term_fv t1) (remove v (term_fv t2))
  | Tif f t1 t2 => union (form_fv f) (union (term_fv t1) (term_fv t2))
  | Tmatch t ty l => union (term_fv t) (big_union (fun x => remove_all (pat_fv (fst x)) (term_fv (snd x))) l)
  end

with form_fv (f: formula) : list vsymbol :=
  match f with
  | Fpred p tys tms => big_union term_fv tms
  | Fquant q v _ f => remove v (form_fv f)
  | Feq _ t1 t2 => union (term_fv t1) (term_fv t2)
  | Fbinop b f1 f2 => union (form_fv f1) (form_fv f2)
  | Fnot f => form_fv f
  | Ftrue => nil
  | Ffalse => nil
  | Flet t v _ f => union (term_fv t) (remove v (form_fv f))
  | Fif f1 f2 f3 => union (form_fv f1) (union (form_fv f2) (form_fv f3))
  | Fmatch t ty l => union (term_fv t) (big_union (fun x => remove_all (pat_fv (fst x)) (form_fv (snd x))) l)
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

Definition indpreds_of_def (d: def) : list (predsym * list formula) :=
  match d with
  | inductive_def li =>
    fold_right (fun x acc => 
    match x with
    | ind_def p fs => (p, fs) :: acc
    end) nil li
  | _ => nil
  end.

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
  | inductive_def inds => map (fun a =>
    match a with
    | ind_def ps _ => ps
    end) inds
  end.