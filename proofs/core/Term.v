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

(* We handle function/predicate symbols specially. A function symbol
   contains a name, a list of arguments (which must be value types),
   and the return type, which can be a value type or a prop.
   As far as I can tell, why3 does not allow partial application of these
   functions, but our core language will (this is OK; we will ensure
   through the translation and type system that no partially applied
   terms remain in a well-typed term (TODO: IS THIS OK?))
   We will have a funsym contain both the types which have already been
   applied and the return type, which can be a function or a type*)

(* We split function and predicate symbols to help with the logic part *)
Record funsym :=
  {
    s_args: list vty;
    s_ret: vty
  }.

Record predsym :=
  {
    p_args : list vty
  }.

(*Generalized logic symbol*)
Inductive lsym :=
  | l_func : funsym -> lsym
  | l_pred : predsym -> lsym.

(*We need more than terms - need decls as well - this way we know
  axioms, lemmas, goals, function bodies*)

(*
Definition app_one (s: sym) : option funsym :=
  match (s_args f) with
  | nil => None
  | a :: args => Some (mk_sym (fs_name f) (fs_applied f ++ (a :: nil)) args (fs_val f))
  end.
*)
Inductive constant : Type :=
  | ConstInt : Z -> constant
  | ConstReal : R -> constant
  | ConstStr : string -> constant.

(*function/predicate symbol: has arguments and return value*)
(*Unfortunately, we do need the list (we can't just curry/uncurry)
  because of the vty/ty distinction - we cannot have functions 
  which take props as input*)

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
  | Tapp: lsym -> list term -> term
  | Tif: term -> term -> term -> term
  (*NOTE: for now: do NOT include let - we will translate it
    as a lambda (which uses Teps) instead at a higher level.
    It makes the binders more complicated (TODO: is there a simpler way?)*)
  | Tlet : term -> term -> term
  | Teps: term -> term (*TODO: is this the case? can we do let like this?*)
  | Tquant: quant -> term -> term
  | Tbinop: binop -> term -> term -> term
  | Tnot: term -> term
  | Ttrue: term
  | Tfalse: term.

(*TODO: redo better induction principle, prove things for substitution *)

Inductive prop_kind :=
  | Plemma (*prove, use as a premise*)
  | Paxiom (*do not prove, use as a premise*)
  | Pgoal. (*prove, do not use as a premise*)

(*For now (do later) skipping recursive algebraic datatypes, inductive predicates*)
Inductive decl : Type :=
  | Dtype: typesym -> decl (*abstract types*)
  | Dparam: lsym -> decl (*abstract functions and predicates*)
  | Dlogic: lsym -> term -> decl (*recursive functions and predicates*)
  | Dprop: prop_kind -> term -> decl. (*axiom/lemma/goal*)

(*Modelling a theory very simply: a theory can other theories and has
  a list of decls. We ignore cloning for now*)
Inductive theory : Type :=
  | Decls: list decl -> theory
  | Use: theory -> theory.
(*It's all just a list of decls in this notation*)

(*TODO: we want to define what it means for a Dprop decl to be true.
  To do this, we will need variable binding, types for terms, and lots
  of other things, but we first want to sketch out the structure*)

(* Uninterpreted Predicates *)
(* The only information we can get comes from axioms. We first extract
   the axioms, then give a definition for uninterpreted predicates
   (TODO: work in progress, need to think about uninterpreted functions,
      use of uninterpred predicates in terms)*)

Definition get_axioms (l: list decl) : list term := fold_right (fun d acc =>
  match d with
  | Dprop (Paxiom) t => t :: acc
  | _ => acc
  end) nil l.

(* The idea is that we map the predicate/function symbols to Coq functions. 
   We will universally quantify over this map, so something will only be
   true if it is true for every possible interpretation of this function. *)
Record map_uninterp: Type := {
  map_upred : predsym -> (list term -> Prop);
  map_ufunc : funsym -> (list term -> term)
}.

Definition andl (l: list Prop) : Prop :=
  fold_right and True l.

(*Transform a term according to the uninterpreted function map*)
Definition transform_term (m: map_uninterp) (t: term) : term.
Admitted.

(*TODO: this stuff may have to be mutually recursive/may need relation*)
(*I really do need to write this to see how it will look*)
(*Idea: take term of type bool, give proposition that this term corresponds to*)
Definition term_prop (ctx: list decl) (t: term) : Prop.
Admitted.

(*In reality, should FIRST substitute with map, then quantify over everything, I think*)
(*The idea is that, if *)
Definition upred_prop (ctx: list decl) (p: predsym) (args: list term) : Prop :=
  (*not quite: need previous contexts for each mapping*)
  forall (m: map_uninterp), 
  andl (List.map (term_prop ctx (*WRONG!*)) 
    (List.map (transform_term m) (get_axioms ctx))) ->
  (map_upred m) p args.
(*
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
*)
Fixpoint traverse_term (f: nat -> nat -> term) l t :=
  match t with
  | Tvar x => f l x
  | Tapp t1 t2 => Tapp (traverse_term f l t1) (traverse_term f l t2)
  | Tif t1 t2 t3 => Tif (traverse_term f l t1) (traverse_term f l t2) (traverse_term f l t3)
  | Tlet t1 t2 => Tlet (traverse_term f l t1) (traverse_term f (1 + l) t2)
  | Teps t => Teps (traverse_term f (1 + l) t)
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
#[local]Instance TraverseVarInjective_term : @TraverseVarInjective term _ term _.
Proof.
  constructor. prove_traverse_var_injective.
Qed.

#[local]Instance TraverseFunctorial_term : @TraverseFunctorial term _ term _.
Proof.
  constructor. prove_traverse_functorial.
Qed.

#[local]Instance TraverseRelative_term : @TraverseRelative term term _.
Proof.
  constructor. prove_traverse_relative.
Qed.

#[local]Instance TraverseIdentifiesVar_term : @TraverseIdentifiesVar term _ _.
Proof.
  constructor. prove_traverse_identifies_var.
Qed.

#[local]Instance TraverseVarIsIdentity_term : @TraverseVarIsIdentity term _ term _.
Proof.
  constructor. prove_traverse_var_is_identity.
Qed.

(* Reduction and Semantics *)

(* There are two different things we want to say about terms: when does a term
   beta-reduce to another term, and when is a proposition true? We handle each
   separately.*)

(* First-order Logic *)

(* Interpretations*)
Definition psym_interp : Type := funsym -> Prop.







(* Idea: each fully-applied funsym of type pred is either true or false *)
(*Axiom funsym_interp *)

(*TODO: should this be list of terms? Or list of Props?*)
Inductive impl : list Prop -> term -> Prop :=
  | T_True: forall l, impl l Ttrue
  | T_Funsym: forall l f, 
    andl -> 


Inductive step : term -> term -> Prop :=
  (* One step of application: apply a single argument *)
  | S_App: forall (f1 f2: funsym) (t: term),
    app_one f1 = Some f2 ->
    step (Tapp (Tfunsym f1) t) (Tfunsym f2)
  | S_ 




  apply map_inj in H3. auto.
  intros x y Hinl _ Heq. rewrite Forall_forall in H0.
  (*TODO: start here (likely) - or is there a better way to handle function predicates?*)
  
  apply (H0 x Hinl y l1).
Admitted.