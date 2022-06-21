Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Lia.
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
    s_name : string;
    s_args: list vty;
    s_ret: vty
  }.

Record predsym :=
  {
    p_name: string;
    p_args : list vty
  }.

(*Generalized logic symbol*)
Inductive lsym :=
  | l_func : funsym -> lsym
  | l_pred : predsym -> lsym.

Definition lsym_name (l: lsym) : string :=
  match l with
  | l_func f => s_name f
  | l_pred p => p_name p
  end.

Definition lsym_eq (l1 l2: lsym) : bool :=
  string_dec (lsym_name l1) (lsym_name l2).

(*We need more than terms - need decls as well - this way we know
  axioms, lemmas, goals, function bodies*)

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

Unset Elimination Schemes.
(* A simplified term language using nats for binders *)
Inductive term : Type :=
  | Tvar: nat -> term
  | Tconst: constant -> term
  | Tlapp: lsym -> list term -> term (*apply arguments to lsym*)
  | Tapp: term -> term -> term (*function application*)
  | Tif: term -> term -> term -> term
  | Tlet : term -> term -> term
  | Tabs : term -> term (*For now, we include lambda and not epsilon*)
  (*| Teps: term -> term *)
  | Tquant: quant -> term -> term
  | Tbinop: binop -> term -> term -> term
  | Teq: term -> term -> term (*builtin to why3, but not a separate term AST node*)
  | Tnot: term -> term
  | Ttrue: term
  | Tfalse: term.
Set Elimination Schemes.

Inductive prop_kind :=
  | Plemma (*prove, use as a premise*)
  | Paxiom (*do not prove, use as a premise*)
  | Pgoal. (*prove, do not use as a premise*)

(*For now (do later) skipping recursive algebraic datatypes, inductive predicates*)
Inductive decl : Type :=
  | Dtype: typesym -> decl (*abstract types*)
  | Dparam: lsym -> decl (*abstract functions and predicates*)
  | Dlogic: lsym -> term -> decl (*recursive functions and predicates*)
    (*this term should be a (closed) lambda abstraction with |s/p_args| arguments.
    We will need to enforce this at the type level*)
  | Dprop: prop_kind -> term -> decl. (*axiom/lemma/goal*)

(*Modelling a theory very simply: a theory can other theories and has
  a list of decls. We ignore cloning for now*)
Inductive theory : Type :=
  | Decls: list decl -> theory
  | Use: theory -> theory.
(*It's all just a list of decls in this notation*)

(* First step: better induction principle *)
Section BetterTermInd.

Variable P: term -> Prop.
Variable Hvar: forall n, P (Tvar n).
Variable Hconst: forall c, P (Tconst c).
Variable Hlapp: forall (ls: lsym) (l: list term),
  Forall P l -> P (Tlapp ls l).
Variable Happ: forall (t1 t2: term),
  P t1 -> P t2 -> P (Tapp t1 t2).
Variable Hif: forall t1 t2 t3,
  P t1 -> P t2 -> P t3 -> P (Tif t1 t2 t3).
Variable Hlet: forall t1 t2,
  P t1 -> P t2 -> P (Tlet t1 t2).
Variable Habs: forall t,
  P t -> P (Tabs t).
Variable Hquant: forall q t,
  P t -> P (Tquant q t).
Variable Hbinop: forall b t1 t2,
  P t1 -> P t2 -> P(Tbinop b t1 t2).
Variable Heq: forall t1 t2,
  P t1 -> P t2 -> P(Teq t1 t2).
Variable Hnot: forall t, P t -> P(Tnot t).
Variable Htrue: P Ttrue.
Variable Hfalse: P Tfalse.

Fixpoint term_ind (t: term) : P t :=
  match t with
  | Tvar n => Hvar n
  | Tconst c => Hconst c
  | Tlapp f l => Hlapp f l 
    ((fix list_term_ind (lt: list term) : Forall P lt :=
    match lt with
    | nil => (@Forall_nil term P)
    | (x :: tl) => @Forall_cons term P _ _ (term_ind x) (list_term_ind tl)
    end) l)
  | Tapp t1 t2 => Happ t1 t2 (term_ind t1) (term_ind t2)
  | Tif t1 t2 t3 => Hif t1 t2 t3 (term_ind t1) (term_ind t2) (term_ind t3)
  | Tlet t1 t2 => Hlet t1 t2 (term_ind t1) (term_ind t2)
  | Tabs t => Habs t (term_ind t)
  | Tquant q t => Hquant q t (term_ind t)
  | Tbinop b t1 t2 => Hbinop b t1 t2 (term_ind t1) (term_ind t2)
  | Teq t1 t2 => Heq t1 t2 (term_ind t1) (term_ind t2)
  | Tnot t => Hnot t (term_ind t)
  | Ttrue => Htrue
  | Tfalse => Hfalse
  end.

End BetterTermInd.

(* Second: define traversal and prove lemmas*)

(* For DBLib library (capture avoiding substitution)*)
Fixpoint traverse_term (f: nat -> nat -> term) l t :=
  match t with
  | Tvar x => f l x
  | Tlapp ls ts => Tlapp ls (List.map (traverse_term f l) ts)
  | Tapp t1 t2 => Tapp (traverse_term f l t1) (traverse_term f l t2)
  | Tif t1 t2 t3 => Tif (traverse_term f l t1) (traverse_term f l t2) (traverse_term f l t3)
  | Tlet t1 t2 => Tlet (traverse_term f l t1) (traverse_term f (1 + l) t2)
  | Tabs t => Tabs (traverse_term f (1 + l) t)
  | Tquant q t => Tquant q (traverse_term f (1 + l) t) 
  | Tbinop b t1 t2 => Tbinop b (traverse_term f l t1) (traverse_term f l t2)
  | Teq t1 t2 => Teq (traverse_term f l t1) (traverse_term f l t2)
  | Tnot t => Tnot (traverse_term f l t)
  | _ => t
  end.

#[local]Instance Var_term : Var term := {
  var := Tvar
}.

#[local]Instance Traverse_term : Traverse term term := {
  traverse := traverse_term
}.

(* The proofs are all a bit more complicated because of the
  Tlapp case. But they are all solved essentially by comparing the
  lists elementwise and using the Forall induction hypothesis *)

#[local]Instance TraverseVarInjective_term : @TraverseVarInjective term _ term _.
Proof.
  constructor. prove_traverse_var_injective.
  subst. simpl in *.
  assert (Hlen: length l = length l1). {
    erewrite <- (map_length _ l). rewrite H3, map_length; reflexivity.
  }
  apply list_eq_ext'; auto.
  intros n d Hn.
  apply (f_equal (fun x => nth n x d)) in H3.
  erewrite !map_nth_inbound in H3; try lia.
  rewrite Forall_forall in H0. apply H0 in H3. apply H3.
  apply nth_In. assumption.
Qed.

#[local]Instance TraverseFunctorial_term : @TraverseFunctorial term _ term _.
Proof.
  constructor. prove_traverse_functorial.
  rewrite Forall_forall in H.
  apply list_eq_ext'; rewrite !map_length. reflexivity.
  intros n d Hn. rewrite !map_nth_inbound with (d1:=d) (d2:=d); auto.
  apply H. apply nth_In. assumption.
  rewrite map_length; assumption.
Qed.

#[local]Instance TraverseRelative_term : @TraverseRelative term term _.
Proof.
  constructor. prove_traverse_relative.
  f_equal. apply list_eq_ext'; rewrite !map_length. reflexivity.
  intros n d Hn. rewrite !map_nth_inbound with (d1:=d)(d2:=d); auto.
  rewrite Forall_forall in H; apply H; auto. apply nth_In; auto.
Qed.

#[local]Instance TraverseIdentifiesVar_term : @TraverseIdentifiesVar term _ _.
Proof.
  constructor. prove_traverse_identifies_var.
Qed.

#[local]Instance TraverseVarIsIdentity_term : @TraverseVarIsIdentity term _ term _.
Proof.
  constructor. prove_traverse_var_is_identity.
  apply list_eq_ext'; rewrite !map_length. reflexivity.
  intros n d Hn. rewrite map_nth_inbound with (d1:=d)(d2:=d); auto.
  rewrite Forall_forall in H0; apply H0. apply nth_In; auto.
Qed.

(* Type system *)

(*We need a type system before we give the logic semantics because we need
  to distinguish between propositions and value types (in particular, we cannot
  quantify over propositions). We could do this by giving a separate inductive
  type for terms and formulas, but because of "if" expressions, this would have
  to be mutually recursive, making things more complicated (maybe) *)

(* Semantics for logic fragment *)

(* We want to give a Prop representing the truth of the logic statement.
   But this depends on the context: for example, if we have the
   uninterpreted predicate foo : int -> bool, then foo 3 can be true
   or false depending on the existing axioms about foo.*)

Section FOLSemantics.

 (* The domain always includes ints, reals, bools, and strings. It may contain other types as well.*)
 Inductive dom (A: Type) : Type :=
 | DInt : Z -> dom A
 | Dreal: R -> dom A
 | Dstr : string -> dom A
 | Ddom: A -> dom A.
 
(*An interpretation I includes a base type A, a meaning for each variable,
 a meaning for each function symbol, and a meaning for each predicate symbol*)
(*TODO: need to include int, real, string - these are builtin*)
Record interp (A: Type) :=
 { 
   vars: nat -> dom A;
   funs: funsym -> (list (dom A) -> dom A);
   preds: predsym -> (list (dom A) -> Prop)
 }.

(*Cannot use function because of if statements - the predicate we
 branch on may not be decidable. This has to be mutually recursive
 because of the Fif_t case: it relies on the interepretation of a formula*)

(*Interpretation for binop*)
Definition binop_interp (b: binop) (p1 p2: Prop) : Prop :=
  match b with
  | Tand => p1 /\ p2
  | Tor => p1 \/ p2
  | Timplies => p1 -> p2
  | Tiff => p1 <-> p2
  end.

(*Here, we use term in the FOL sense, not in the why3 sense*)
Inductive term_interp {A: Type} (i: interp A) : term -> (dom A) -> Prop :=
  | TI_var: forall x,
    term_interp i (Tvar x) (i.(vars _) x)
  | TI_constInt: forall z,
    term_interp i (Tconst (ConstInt z)) (DInt A z)
  | TI_constReal: forall r,
    term_interp i (Tconst (ConstReal r)) (Dreal A r)
  | TI_constStr: forall s,
    term_interp i (Tconst (ConstStr s)) (Dstr A s)
  | TI_fun: forall fsym ts ds,
    Forall (fun x => term_interp i (fst x) (snd x)) (combine ts ds) ->
    term_interp i (Tlapp (l_func fsym) ts) ((funs _ i) fsym ds)
  | TI_if_true: forall t1 t2 t3 p d,
    form_interp i t1 p ->
    p ->
    term_interp i t2 d ->
    term_interp i (Tif t1 t2 t3) d 
  | TI_if_false: forall t1 t2 t3 p d,
    form_interp i t1 p ->
    ~ p ->
    term_interp i t3 d ->
    term_interp i (Tif t1 t2 t3) d
  | TI_let: forall t1 t2 d, (*let x = t1 in t2*)
      term_interp i (subst t1 0 t2) d ->
      term_interp i (Tlet t1 t2) d
with form_interp {A: Type} (i: interp A) : term -> Prop -> Prop :=
  | FI_true:
    form_interp i Ttrue True
  | FI_false:
    form_interp i Tfalse False
  | FI_pred: forall psym ts ds,
    Forall (fun x => term_interp i (fst x) (snd x)) (combine ts ds) ->
    form_interp i (Tlapp (l_pred psym) ts) ((preds _ i) psym ds)
  | FI_not: forall f p,
    form_interp i f p ->
    form_interp i (Tnot f) (~p)
  | FI_binop: forall b f1 f2 p1 p2,
    form_interp i f1 p1 ->
    form_interp i f2 p2 ->
    form_interp i (Tbinop b f1 f2) (binop_interp b p1 p2)
  | FI_eq: forall t1 t2 d1 d2,
    term_interp i t1 d1 ->
    term_interp i t2 d2 ->
    form_interp i (Teq t1 t2) (d1 = d2)
  | FI_if: forall f1 f2 f3 p1 p2 p3,
    form_interp i f1 p1 ->
    form_interp i f2 p2 ->
    form_interp i f3 p3 ->
    form_interp i (Tif f1 f2 f3) ((p1 -> p2) /\ (~p1 -> p3))
  | FI_let: forall t f d p,
    term_interp i t d ->
    form_interp i (subst t 0 f) p ->
    form_interp i (Tlet t f) p
  | FI_forall: forall f,
    (forall x, form_interp i (subst x 0 f) True) ->
    form_interp i (Tquant Tforall f) True
  | FI_forall_fls: forall f,
    (exists x, form_interp i (subst x 0 f) False) ->
    form_interp i (Tquant Tforall f) False
  | FI_exists: forall f,
    (exists x, form_interp i (subst x 0 f) True) ->
    form_interp i (Tquant Texists f) True
  | FI_exists_fls: forall f,
    (forall x, form_interp i (subst x 0 f) False) ->
    form_interp i (Tquant Texists f) False
  | FI_change_prop: forall f p1 p2,
    p1 <-> p2 -> 
    form_interp i f p1 ->
    form_interp i f p2.
(*Without the IF cases, this could be a function. That would be MUCH nicer.*)
(*TODO: do we need false cases for quantifiers?*)

(*Note: this is WRONG! This allows us to quantify over propositions, and it is
  too strong. We will need to distinguish between values and propositions, either
  via a type system or with the actual inductive types.*)

(*Some notation:*)
Notation "i '|=' f" := (form_interp i f True) (at level 40).
Notation "i '|/=' f" := (form_interp i f False) (at level 40).

(*Let's give an example:*)
Lemma prove_eq_refl: forall (A: Type) (i: interp A),
 i |= (Tquant Tforall (Teq (Tvar 0) (Tvar 0))).
Proof.
  intros A i. constructor. intros x.
  simpl_subst_goal.
  econstructor.
  2 : constructor.
Abort.

(*Some definitions in progress/ideas/sketches: *)
(*
Definition context : Type := list decl.

Definition get_lterm_body (l: lsym) (ctx : context) : option term :=
  fold_right (fun x acc =>
    match x with
    | Dtype _ => acc
    | Dparam _ => acc
    | Dlogic ls t => if lsym_eq l ls then Some t else acc
    | Dprop _ _ => acc
    end) None ctx.

(*Before reduction, need to define traverse*)


(*Reduction for value terms*)
(*Our reduction relation requires a context because we need to substitute the
  bodies of known lterms*)
Definition red : ctx -> term -> term -> Prop
| R_

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
  fold_right and True l`.

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
*)
