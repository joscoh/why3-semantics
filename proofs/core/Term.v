Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
From Dblib Require Import DblibTactics DeBruijn Environments.
(* A smaller core language of types and terms *)

Require Import Util.

(*Type variable (ex: a)*)
Definition typevar : Type := string. 

(*Type symbol (ex: list a)*)
Record typesym : Type := {
  ts_name : string;
  ts_args: list typevar 
}.

(*Value types*)
Inductive vty : Type :=
  | vty_int : vty
  | vty_real : vty
  | vty_bool : vty
  | vty_func: vty -> vty -> vty
  | vty_pred: vty -> vty
  | vty_tuple: vty -> vty -> vty
  | vty_var: typevar -> vty
  | vty_app: typesym -> list vty -> vty. (*TODO: do we need this? Can we make it non-list?*)

(*Everything is either a value or a prop*)
Inductive ty : Type :=
  | ty_val : vty -> ty
  | ty_prop : ty.

Inductive constant : Type :=
  | ConstInt : Z -> constant
  | ConstReal : R -> constant
  | ConstStr : string -> constant.

(*function/predicate symbol: has arguments and return value*)
(*Unfortunately, we do need the list (we can't just curry/uncurry)
  because of the vty/ty distinction - we cannot have functions 
  which take props as input*)
Record funsym :=
  {
    fs_name : string;
    fs_args: list vty;
    fs_val: ty
  }.

Inductive quant : Type :=
    | Tforall
    | Texists.

Inductive binop : Type :=
    | Tand
    | Tor
    | Timplies
    | Tiff.

(* A simplified term language using nats for binders *)
Inductive term : Type :=
  | Tvar: nat -> term
  | Tconst: constant -> term
  | Tapp: funsym -> list term -> term
  | Tif: term -> term -> term -> term
  (*NOTE: for now: do NOT include let - we will translate it
    as a lambda (which uses Teps) instead at a higher level.
    It makes the binders more complicated (TODO: is there a simpler way?)*)
  | Teps: term -> term (*TODO: is this the case? can we do let like this?*)
  | Tquant: quant -> term -> term
  | Tbinop: binop -> term -> term -> term
  | Tnot: term -> term
  | Ttrue: term
  | Tfalse: term.

(*Better induction principle*)
Section BetterTermInd.

Variable P: term -> Prop.
Variable Hvar: forall n, P (Tvar n).
Variable Hconst: forall c, P (Tconst c).
Variable Happ: forall (f: funsym) (l: list term),
  Forall P l -> P (Tapp f l).
Variable Hif: forall t1 t2 t3,
  P t1 -> P t2 -> P t3 -> P (Tif t1 t2 t3).
Variable Heps: forall t,
  P t -> P (Teps t).
Variable Hquant: forall q t,
  P t -> P (Tquant q t).
Variable Hbinop: forall b t1 t2,
  P t1 -> P t2 -> P(Tbinop b t1 t2).
Variable Hnot: forall t, P t -> P(Tnot t).
Variable Htrue: P Ttrue.
Variable Hfalse: P Tfalse.

Fixpoint term_ind' (t: term) : P t :=
  match t with
  | Tvar n => Hvar n
  | Tconst c => Hconst c
  | Tapp f l => Happ f l 
    ((fix list_term_ind (lt: list term) : Forall P lt :=
    match lt with
    | nil => (@Forall_nil term P)
    | (x :: tl) => @Forall_cons term P _ _ (term_ind' x) (list_term_ind tl)
    end) l)
  | Tif t1 t2 t3 => Hif t1 t2 t3 (term_ind' t1) (term_ind' t2) (term_ind' t3)
  | Teps t => Heps t (term_ind' t)
  | Tquant q t => Hquant q t (term_ind' t)
  | Tbinop b t1 t2 => Hbinop b t1 t2 (term_ind' t1) (term_ind' t2)
  | Tnot t => Hnot t (term_ind' t)
  | Ttrue => Htrue
  | Tfalse => Hfalse
  end.

End BetterTermInd.

Fixpoint traverse_term (f: nat -> nat -> term) l t :=
  match t with
  | Tvar x => f l x
  | Tapp fs lt => Tapp fs (List.map (traverse_term f l) lt)
  | Tif t1 t2 t3 => Tif (traverse_term f l t1) (traverse_term f l t2) (traverse_term f l t3)
  | Teps t => Teps (traverse_term f l t)
  | Tquant q t => Tquant q (traverse_term f (1 + l) t) 
  | Tbinop b t1 t2 => Tbinop b (traverse_term f l t1) (traverse_term f l t2)
  | Tnot t => Tnot (traverse_term f l t)
  | _ => t
  end.

(*Problem is that induction principle is too weak: need better term induction. *)

#[local]Instance Var_term : Var term := {
  var := Tvar
}.

#[local]Instance Traverse_term : Traverse term term := {
  traverse := traverse_term
}.

Lemma map_inj: forall {A B: Type} (f: A -> B) (l1 l2: list A),
  (forall x y, In x l1 -> In y l1 -> f x = f y -> x = y) ->
  List.map f l1 = List.map f l2 ->
  l1 = l2.
Admitted.

(*
Lemma traverse_term_inj: forall f l t1 t2,
  (forall x1 x2 l, f l x1 = f l x2 -> x1 = x2) ->
  traverse_term f l t1 = traverse_term f l t2 ->
  t1 = t2.
Proof.
  prove_traverse_var_injective.
  intros f l t1. induction t1 using term_ind'; intros t2 Hinj; destruct t2; simpl;
  intros Heq; try solve[inversion Heq]; try solve[reflexivity].
  - apply Hinj in Heq; auto.
  - 
  inversion Heq; subst; try reflexivity.
  - apply Hinj in H0; auto.
  - 
*)
(*This is a hack*) 
Ltac prove_traverse_var_injective ::=
  let t1 := fresh "t1" in
  intros ? ? t1; induction t1 using term_ind';
   (let t2 := fresh "t2" in
	intro t2; destruct t2; simpl;
     (let h := fresh "h" in
      intros ? h; inversion h; f_equal; eauto using @traverse_var_injective
       with typeclass_instances)).
#[local]Instance TraverseVarInjective_term : @TraverseVarInjective term _ term _.
Proof.
  constructor. prove_traverse_var_injective.
  apply map_inj in H3. auto.
  intros x y Hinl _ Heq. rewrite Forall_forall in H0.
  (*TODO: start here (likely) - or is there a better way to handle function predicates?*)
  
  apply (H0 x Hinl y l1).
Admitted.