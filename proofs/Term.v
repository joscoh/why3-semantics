Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Reals.Reals.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapAVL.
Require Import Lia.

Require Import Util.
Require Import Ty.

(* Constants *)
(* Constants in Why3 are a bit more complicated (for ints, they distinguish
between decimal, hex, etc and for reals, it uses a mantissa and exponent)
    For the moment, we just model these as coq Z and R types. This can always
    be changed in the future. *)

Inductive constant : Type :=
    | ConstInt : Z -> constant
    | ConstReal : R -> constant
    | ConstStr : string -> constant.


(* Variable Symbols *)

(*Private*)
Record vsymbol : Type := mk_vsym { vs_name : ident; vs_ty : ty }.

Definition vsymbol_eq_dec : forall (v1 v2: vsymbol), {v1 = v2} + {v1 <> v2}.
Proof.
    decide equality.
    apply ty_eq_dec.
    apply ident_eq_dec.
Defined.

(*Not going through all the indirection, just giving an ordered type directly*)
(*TODO: do on vsymbol*)
Module VSymbolOrderedType <: OrderedType.

Local Open Scope Z_scope.

Definition t := vsymbol.
Definition eq (v1 v2: t) := (id_tag (vs_name v1)) = (id_tag (vs_name v2)).
Definition lt (v1 v2: t) := (id_tag (vs_name v1)) < (id_tag (vs_name v2)).

Lemma eq_refl: forall x : t, eq x x.
Proof. congruence. Qed.

Lemma eq_sym: forall x y : t, eq x y -> eq y x.
Proof. congruence. Qed.

Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. congruence. Qed.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. unfold lt; lia. Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. unfold lt, eq; lia. Qed.

Definition compare : forall x y : t, Compare lt eq x y.
intros x y.
destruct (Z.eq_dec (id_tag (vs_name x)) (id_tag (vs_name y))); [| 
    destruct (Z_lt_dec (id_tag (vs_name x)) (id_tag (vs_name y)))].
- apply EQ. assumption.
- apply LT. assumption.
- apply GT. unfold lt; lia.
Defined.

Lemma eq_dec : forall x y, { eq x y } + { ~ eq x y }.
Proof.
    intros x y; unfold eq; apply Z.eq_dec.
Qed.

End VSymbolOrderedType.

(*Map for variable substition*)
(* Why3 uses OCaml's map. We use Coq's FMap.AVL on ordered keys, which is designed
   to be similar to OCaml's. The Why3 version includes extra functions, we do not
   at the moment *)
Module Mvs := FMapAVL.Make VSymbolOrderedType.

(*We also need a set of keys. Why3 does this by implementing the set interface
    using their map implementation. For now, we just use a list (TODO: change later) *)

(* Function and Predicate Symbols *)

(*Private*)
Record lsymbol : Type := mk_lsym {
    ls_name : ident;
    ls_args: list ty;
    ls_value : option ty;
    ls_constr: Z
}.

Definition lsym_with_args (l: lsymbol) (tys: list ty) :=
    mk_lsym (ls_name l) tys (ls_value l) (ls_constr l).

(* Patterns *)
Inductive pattern :=
    | mk_pattern : pattern_node -> list vsymbol -> ty -> pattern
with pattern_node :=
    | Pwild : pattern_node (* _ *)
    | Pvar : vsymbol -> pattern_node (*newly introduced variables*)
    | Papp : lsymbol -> list pattern -> pattern_node (*application*)
    | Por : pattern -> pattern -> pattern_node (* | *)
    | Pas : pattern -> vsymbol -> pattern_node
    (*naming a term recognized by a pattern as a variable*).

(* Terms and Formulas *)

Inductive quant : Type :=
    | Tforall
    | Texists.

Inductive binop : Type :=
    | Tand
    | Tor
    | Timplies
    | Tiff.

(* The OCaml definition, ignoring attributes and location, is:

(*Ignore attributes and location *)
Inductive term : Type := (* private *)
    | mk_term : term_node -> option ty -> term
with term_node : Type :=
    | Tvar : vsymbol -> term_node
    | Tconst : constant -> term_node
    | Tapp: lsymbol -> list term -> term_node
    | Tif: term -> term -> term -> term_node
    | Tlet: term -> term_bound -> term_node
    | Tcase: term -> list term_branch -> term_node
    | Teps: term_bound -> term_node
    | Tquant: quant -> term_quant -> term_node
    | Tbinop: binop -> term -> term -> term_node
    | Tnot: term -> term_node
    | Ttrue
    | Tfalse
with term_bound : Type :=
    | mk_termbnd : (vsymbol * bind_info * term) -> term_bound
with term_branch : Type :=
    | mk_termbranch: pattern -> bind_info -> term -> term_branch
with term_quant : Type :=
    | mk_termquant: list vsymbol -> bind_info -> list (list term) -> term -> term_quant
with bind_info : Type :=
    | mk_bindinfo : Mvs.t Z -> list (vsymbol * term) -> bind_info.
*)

(*Our definition has no mutual recursion*)
Inductive term : Type :=
    | Tvar : vsymbol -> option ty -> term
    | Tconst: constant -> option ty -> term
    | Tapp: lsymbol -> list term -> option ty -> term
    | Tif: term -> term -> term -> option ty -> term
    | Tlet: term -> (vsymbol * (Mvs.t Z * list (vsymbol * term)) * term) -> option ty -> term
    | Tcase: term -> list (pattern * (Mvs.t Z * list (vsymbol * term)) * term) -> option ty -> term
    | Teps: (vsymbol * (Mvs.t Z * list (vsymbol * term)) * term) -> option ty -> term
    | Tquant: quant -> (list vsymbol * (Mvs.t Z * list (vsymbol * term)) * list (list term) * term) ->
        option ty -> term
    | Tbinop: binop -> term -> term -> option ty -> term
    | Tnot: term -> option ty -> term
    | Ttrue : option ty -> term
    | Tfalse : option ty -> term.

(*Notations to make definition much nicer (and equivalent to above, just with
  added [option ty])*)
Notation bind_info := (Mvs.t Z * list (vsymbol * term))%type.
Notation term_bound := (vsymbol * bind_info * term)%type.
Notation term_branch := (pattern * bind_info * term)%type.
Notation term_quant := (list vsymbol * bind_info * list (list term) * term)%type.


(*In the OCaml code, some of these are defined with records.
  We couldn't do that because we define everything inductively. But we can
  do it now.*)

(*For terms: *)
(*
Definition t_node (t: term) : term_node :=
    match t with
    | mk_term tn _ => tn
    end.
Coercion t_node : term >-> term_node.*)

(*For term_bound:*)
(*
Definition term_bound_info (t: term_bound) : vsymbol * bind_info * term :=
    match t with
    | mk_termbnd x => x
    end.
*)

(*NOTE: in bind_info, the why3 definition is in a map (MVS.t), 
    but this violates Coq's positivity check, so we use a manual
    association list and convert back and forth (TODO: for now)
    see: https://stackoverflow.com/questions/49844617/why-fmapavl-usage-in-argument-is-non-strictly-positive-while-list-is*)

(*TODO: define typing, substitution, etc*)

(*Now we want to define the type of a term.
  In the why3 implementation, each team has a ty option, where
  props have type None, and everything else has Some (type of term).
  We will use this relation to prove that all "smart constructors"
  produce well-typed terms. *)
(*
Inductive full_ty : Type :=
    | Fty : ty -> full_ty
    | Fprop : full_ty.

Definition get_full_ty (t: option ty) :=
    match t with
    | None => Fprop
    | Some typ => Fty typ
    end.
*)
(*Definition full_ty_opt (f: full_ty) : option ty :=
    match f with
    | Fty t => Some t
    | Fprop => None
    end.*)

(*From Software Foundations, Maps.v *)
Definition partial_map (A: Type) := vsymbol -> (option A).
Definition context := partial_map ty.
Definition update {A: Type} (p: partial_map A) (v: vsymbol) (a: A) :=
    fun v' => if vsymbol_eq_dec v v' then (Some a) else (p v').
    (*TODO: do we want to include the type in this too? Does it matter?*)
Definition empty : context := fun _ => None.

(*Definition all_true (l: list Prop) : Prop :=
    fold_right (fun x acc => x /\ acc) True l.
*)
(*TODO: is it a problem to statically require the types in the option?*)
(*We do not need a typing context (I believe), because each vsymbol is
  annotated with its type. Thus, there is no ambiguity for variable x;
  we can always determine its type.
  We include the redundant type information because it makes some of the 
  definitions easier, and we can prove that the OCaml code actually
  has correct type annotations*)
Inductive has_type : term -> option ty -> Prop :=
    | T_Var : forall x,
        has_type (Tvar x (Some (vs_ty x))) (Some (vs_ty x))
    | T_ConstInt : forall (z: Z),
        has_type (Tconst (ConstInt z) (Some ty_int)) (Some ty_int)
    | T_ConstReal : forall (r: R),
        has_type (Tconst (ConstReal r) (Some ty_real)) (Some ty_real)
    | T_ConstStr : forall (s: string),
        has_type (Tconst (ConstStr s) (Some ty_str)) (Some ty_str)
    (*Application is a bit more difficult. Why3 allows a list of
      arguments, and directly recursing violates Coq's positivity checker.
      Instead, we recurse on the list by giving separate nil and cons cases.*)
    | T_AppNil: forall (l: lsymbol),
        ls_args l = nil ->
        has_type (Tapp l nil (ls_value l)) (ls_value l)
        (*NOTE: this is an uninterpreted symbol, so we cannot check the
          term for the function itself. Instead, we "know" that this
          uninterpreted function has type ls_value l if all arguments are
          correct.*)
    | T_AppCons: forall (l: lsymbol) (ts: list term) (hd: term)
        (argshd : ty) (argstl : list ty) (t: option ty),
        ls_args l = argshd :: argstl ->
        has_type hd (Some argshd) -> (*TODO: why doesn't notation work?*)
        has_type (Tapp (lsym_with_args l argstl) ts t) t ->
        has_type (Tapp l (hd :: ts) t) t
    | T_If: forall (f t1 t2: term) (t: option ty),
        has_type f None ->
        has_type t1 t ->
        has_type t2 t ->
        has_type (Tif f t1 t2 t) t
    | T_Let: forall (t: term) (tb: term_bound) (T1 : ty) (t2: option ty),
        vs_ty (fst (fst tb)) = T1 ->
        has_type t (Some T1) ->
        has_type (snd tb) t2 ->
        has_type (Tlet t tb t2) t2
    (* Skipping T_Case for now because Frama-C doesn't use it. Typing
       patterns is complicated*)
    | T_Eps: forall (tb: term_bound),
        let v := fst (fst tb) in
        has_type (snd tb) None ->
        has_type (Teps tb (Some (vs_ty v))) (Some (vs_ty v))
    (* NOTE: I am a bit skeptical of t_quant in the why3 code
       One could produce ill-typed formulas, I believe.
       t_quant_close requires the following to have type None, but not
       t_quant. Both are public, but it seems that t_quant_close is recommended.
       Frama-C uses the _close versions. *)
    | T_QuantNil: forall (q: quant) (tq: term_quant) (t: option ty),
        fst (fst (fst tq)) = nil ->
        has_type (snd tq) t ->
        has_type (Tquant q tq t) t
        (*TODO: this follows code, but is it correct? what about: forall _, 2 + 2.
          Should this be well-typed?*)
    | T_QuantCons: forall (q: quant) (vs: list vsymbol) 
        (b: bind_info) (tr: list (list term)) (t: term),
        has_type t None ->
        has_type (Tquant q (vs, b, tr, t) None) None
    | T_Binop: forall (b: binop) (t1 t2 : term),
        has_type t1 None ->
        has_type t2 None ->
        has_type (Tbinop b t1 t2 None) None
    | T_Not: forall (t: term),
        has_type t None ->
        has_type (Tnot t None) None
    | T_True : 
        has_type (Ttrue None) None
    | T_False: 
        has_type (Tfalse None) None.    

Definition t_ty (t: term) : option ty :=
    match t with
    | Tvar _ x => x
    | Tconst _ x => x
    | Tapp _ _ x => x
    | Tif _ _ _ x => x
    | Tlet _ _ x => x
    | Tcase _ _ x => x
    | Teps _ x => x
    | Tquant _ _ x => x
    | Tbinop _ _ _ x => x
    | Tnot _ x => x
    | Ttrue x => x
    | Tfalse x => x
    end.

Definition well_typed (t: term) := has_type t (t_ty t).

(*We want to prove that the type annotations are correct*)
Lemma type_annot_correct: forall t (o: option ty),
    has_type t o ->
    o = t_ty t.
Proof.
    intros t o Hty. induction Hty; simpl; auto.
Qed.

Lemma has_well_typed: forall t o,
    has_type t o ->
    well_typed t.
Proof.
    unfold well_typed. intros. assert (Hty:=H).
    apply type_annot_correct in H.
    subst. assumption.
Qed.

Lemma well_has_type: forall t o,
    t_ty t = o ->
    well_typed t ->
    has_type t o.
Proof.
    intros. subst. apply H0.
Qed.

Definition well_typed_opt (o: option term) :=
    match o with
    | Some t => well_typed t
    | None => True
    end.

(*Now we define the smart constructors and prove that they
  are all well-typed*)

(*Start with the ones used by why3:*)
(*
t_app_infer
t_app
x t_const
t_quant
t_close_quant
t_true
t_bool_true
t_false
t_bool_false
t_and
t_or
t_not
t_implies
t_iff
t_equ
t_neq
x t_if
t_let_close
x t_var
t_forall_close
t_equal*)

(* Type Checking *)

(* The OCaml code uses exceptions. We could use options, but that would be
   confusing with how prop types are represented. Instead, we give a 
   new datatype *)
(*
Inductive term_ty :=
    | Tm_Val : ty -> term_ty
    | Tm_Prop : term_ty
    | Tm_IllTyped : term_ty.
*)

(* Type checking *)

(* Checks that t is value-typed and returns its type *)
Definition t_type (t: term) : option ty := t_ty t.

(* Checks that t is prop-typed (unlike OCaml, we do not return t) *)
Definition t_prop (t: term) : bool :=
    match t_ty t with
    | None => true
    | Some _ => false
    end.

Lemma t_prop_eq: forall t,
    t_prop t = true <-> t_ty t = None.
Proof.
    intros t. unfold t_prop. destruct (t_ty t) eqn : Hty; simpl.
    split; intros C; inversion C.
    split; reflexivity.
Qed.

(* t_ty_check checks that the type of t is o*)
Definition t_ty_check (t: term) (o: option ty) : bool :=
    match o, t_ty t with
    | Some l, Some r => ty_eqb l r
    | None, None => true
    | _, _ => false
    end.

(*While the above is modelled after the OCaml code, it is really just
  decidable equality*)
Lemma t_ty_check_eq: forall t o,
    t_ty_check t o = true <-> t_ty t = o.
Proof.
    intros t o. unfold t_ty_check. destruct o; destruct (t_ty t) eqn : Hty;
    try solve[split; reflexivity]; try solve[split; intro C; inversion C].
    split; intros Heq.
    - apply ty_eqb_eq in Heq. subst; reflexivity.
    - inversion Heq; subst. apply ty_eqb_refl.
Qed. 

Definition vs_check (v: vsymbol) (t: term) : bool :=
    match (t_type t) with
    | None => false
    | Some ty => ty_eqb (vs_ty v) ty
    end.

Lemma vs_check_true: forall v t,
    vs_check v t = true ->
    t_ty t = Some (vs_ty v).
Proof.
    intros v t. unfold vs_check, t_type.
    destruct (t_ty t) eqn : Hty; [|intro C; inversion C].
    intros Heq. apply ty_eqb_eq in Heq. subst. reflexivity.
Qed.

(* Smart constructors for terms and formulas *)

(* Auxiliary*)
Definition t_const_aux (c: constant) (ty: ty) : term :=
    Tconst c (Some ty).
Definition t_app_aux (f: lsymbol) (tl: list term) (ty: option ty) : term :=
    Tapp f tl ty.
Definition t_if_aux (f t1 t2: term) :=
    Tif f t1 t2 (t_ty t2).
Definition t_let_aux (t1 : term) (bt: term_bound) (ty: option ty) : term :=
    Tlet t1 bt ty.
(*Skip t_case*)
Definition t_eps_aux (bf: term_bound) (ty: option ty) : term :=
    Teps bf ty.
Definition t_quant_aux (q: quant) (qf: term_quant) : term :=
    Tquant q qf None.
Definition t_binary_aux (op: binop) (f g: term) : term :=
    Tbinop op f g None.
Definition t_not_aux (f: term) : term :=
    Tnot f None.

(*Constructors with type checking*)

(*All of the why3 versions return terms. Some of these return [option term]
  because the result may not typecheck, and we don't have exceptions*)

(*TODO: do t_app later, it will be annoying because we need type matching
and then nested recursion over a list*)
(*Definition t_app (ls: lsymbol) (tl: term list) (ty: option ty) : term := *)

(*Lots of the proofs are very repetitive; we define several tactics to handle this*)

(* Get type info into context *)
Ltac get_types :=
    repeat match goal with
    | H: well_typed ?t |- _ =>
        unfold well_typed in H
    end.

(* Solve trivial typing judgements *)
Ltac solve_types :=
    lazymatch goal with
    | H: has_type ?t ?o |- has_type ?t ?p =>
    try apply H;
    let E := fresh in
    assert (E: o = p) by 
    (auto; try congruence); rewrite <- E; apply H
end.

(*Many constructors have the form: if ?x then foo(...) else None*)
(*Additionally, we have results of the form: ?x = true -> ?p*)
Ltac simpl_compound_type :=
    lazymatch goal with
    | H: (if ?f then ?t else None) = Some ?y |- _ =>
        let E := fresh "Hcond" in
        destruct f eqn : E; [|inversion H]
    end.

(*t_prop and t_ty_check are used in some conditions. We can use
  previous lemmas to simplify*)

Ltac simpl_conds :=
    lazymatch goal with
    | H: t_prop ?t = true |- _ => apply t_prop_eq in H
    | H: t_ty_check ?t ?o = true |- _ => apply t_ty_check_eq in H
    | H: vs_check ?v ?t = true |- _ => apply vs_check_true in H
    end.

Ltac unfold_aux :=
    unfold t_const_aux, t_app_aux, t_if_aux, t_let_aux, 
    t_eps_aux, t_quant_aux, t_binary_aux, t_not_aux in *.

(* Handle the repetitive parts in the well-typed proofs *)
Ltac prove_well_typed :=
    intros;
    repeat match goal with
    | |- well_typed_opt ?o => 
        let t := fresh "t" in
        let Hopt := fresh "Hwtopt" in 
        destruct o as [t|] eqn : Hwtopt ;[simpl| apply I]
    | |- well_typed (?x ?y) => unfold x
    | |- well_typed (?a ?b ?c) => unfold a
    end;
    (*unfold in hypotheses*)
    repeat match goal with
    | H : ?f ?x = Some ?t |- _ => unfold f in H
    | H: ?f ?x ?y = Some ?t |- _ => unfold f in H
    | H: ?f ?x ?y ?z = Some ?t |- _ => unfold f in H
    end;
    (*do some simplification*)
    unfold well_typed;
    repeat simpl_compound_type;
    repeat simpl_conds;
    unfold_aux;
    try match goal with
    | H: Some ?x = Some ?y |- _ => inversion H; subst; clear H
    end;
    try solve[constructor; subst; simpl; get_types; solve_types];
    try solve[get_types; solve_types];
    try match goal with
    | |- has_type (Tlet ?t ?tb ?t2) ?o => eapply T_Let;[reflexivity| |];
        subst; simpl; get_types; try solve_types
    end.

(* TODO: this is very repetitive *)

Definition t_var (v: vsymbol) : term :=
    Tvar v (Some (vs_ty v)).

Lemma t_var_ty: forall v,
    well_typed (t_var v).
Proof. prove_well_typed. Qed.

Definition check_literal (c: constant) (ty : ty) : bool :=
    let ts := 
    match ty, c with
    | Tyapp ts nil, _ => Some ts
    | _, _ => None
    end in
    match c, ts with
    | ConstInt _, Some ts => tysymbol_eq_dec ts ts_int
    | ConstReal _, Some ts => tysymbol_eq_dec ts ts_real
    | ConstStr _, Some ts => tysymbol_eq_dec ts ts_str
    | _, _ => false
    end.

(*TODO: move*)
Ltac simpl_sumbool :=
    match goal with
    | [H: proj_sumbool ?x ?y ?z = true |- _ ] => destruct z; inversion H; clear H; subst; auto
    end.

Lemma check_literal_some: forall c ty,
    check_literal c ty = true ->
    (exists z, c = ConstInt z /\ ty = Tyapp ts_int nil) \/
    (exists r, c = ConstReal r /\ ty = Tyapp ts_real nil) \/
    (exists s, c = ConstStr s /\ ty = Tyapp ts_str nil).
Proof.
    intros c ty Hcl. 
    destruct ty; destruct c; try(destruct l); simpl in Hcl; try solve[inversion Hcl];
    simpl_sumbool.
    - left. exists z. split; reflexivity.
    - right. left. exists r. split; reflexivity.
    - right. right. exists s. split; reflexivity.
Qed. 

Definition t_const (c: constant) (ty: ty) : option term :=
    if check_literal c ty then Some (t_const_aux c ty) else None.

Lemma t_const_ty: forall c ty,
    well_typed_opt (t_const c ty).
Proof. 
    prove_well_typed.
    apply check_literal_some in Hcond.
    destruct Hcond as [[z [Hc Hty]] | [[r [Hc Hty]]|[r [Hc Hty]]]]; 
    subst; prove_well_typed.
Qed.

Definition t_if (f t1 t2: term) : option term :=
    if t_ty_check t2 (t_ty t1) then
    if t_prop f then Some (t_if_aux f t1 t2) else None else None.

Lemma t_if_ty: forall f t1 t2,
    well_typed f ->
    well_typed t1 ->
    well_typed t2 ->
    well_typed_opt (t_if f t1 t2).
Proof.
    prove_well_typed.
Qed.

Definition t_let (t1 : term) (bt: term_bound) : option term :=
    if vs_check (fst (fst bt)) t1 then
    Some (t_let_aux t1 bt (t_ty (snd bt))) else None.

Lemma t_let_ty: forall t1 bt,
    well_typed t1 ->
    well_typed (snd bt) ->
    well_typed_opt (t_let t1 bt).
Proof.
    prove_well_typed. 
Qed.

Definition t_eps (bf: term_bound) : option term :=
    if t_prop (snd bf) then Some (t_eps_aux bf (Some (vs_ty (fst (fst bf))))) else None.

Lemma t_eps_ty: forall bf,
    well_typed (snd bf) ->
    well_typed_opt (t_eps bf).
Proof.
    prove_well_typed.
Qed. 

(*TODO: is this type-safe?*)
(*I see: term_quant can only be constructed with t_close_quant, should really
  be considered internal*)
Definition t_quant (q: quant) (qf: term_quant) : term :=
    match (fst(fst(fst qf))) with
    | nil => snd qf
    | _ => t_quant_aux q qf
    end.

Lemma t_quant_ty: forall q qf,
    has_type (snd qf) None ->
    well_typed (t_quant q qf).
Proof.
    prove_well_typed.
    destruct qf as [[[vl x1] x2] f]; simpl in *.
    destruct vl eqn : Hvl; prove_well_typed.
    eapply has_well_typed. apply H.
Qed.

Definition t_forall := t_quant Tforall.

Definition t_exists := t_quant Texists.

Definition t_binary (op: binop) (f1 f2: term) : option term :=
    if (t_prop f1) then
    if (t_prop f2) then
    Some (t_binary_aux op f1 f2) else None else None.

Lemma t_binary_ty: forall op f1 f2,
    well_typed f1 ->
    well_typed f2 ->
    well_typed_opt (t_binary op f1 f2).
Proof.
    prove_well_typed.
Qed.

Definition t_and := t_binary Tand.
Definition t_or := t_binary Tor.
Definition t_implies := t_binary Timplies.
Definition t_iff := t_binary Tiff.

Definition t_not (f: term) :=
    if (t_prop f) then Some (t_not_aux f) else None.

Lemma t_not_ty: forall f,
    well_typed f ->
    well_typed_opt (t_not f).
Proof.
    prove_well_typed.
Qed.

Definition t_true : term := Ttrue None.
Definition t_false : term := Tfalse None.

Lemma t_true_ty: well_typed t_true.
Proof. prove_well_typed. Qed.

Lemma t_false_ty: well_typed t_false.
Proof. prove_well_typed. Qed.

Definition t_nat_const (n: nat) : term :=
    t_const_aux (ConstInt (Z.of_nat n)) ty_int.

Lemma t_nat_const_ty: forall n,
    well_typed (t_nat_const n).
Proof. prove_well_typed. Qed.

Definition t_int_const (z: Z) : term :=
    t_const_aux (ConstInt z) ty_int.

Lemma t_int_const_ty: forall z,
    well_typed (t_int_const z).
Proof. prove_well_typed. Qed.

(*Theirs uses a mantissa and exponent*)
Definition t_real_const (r: R): term :=
    t_const_aux (ConstReal r) ty_real.

Lemma t_real_const_ty: forall r,
    well_typed (t_real_const r).
Proof. prove_well_typed. Qed.

Definition t_string_const (s: string) : term :=
    t_const_aux (ConstStr s) ty_str.

Lemma t_string_const_ty: forall s,
    well_typed (t_string_const s).
Proof. prove_well_typed. Qed.

(*NOT type safe (if list is singleton)*)
Fixpoint t_and_l (l: list term) : option term :=
    match l with
    | nil => Some (t_true)
    | f :: nil => Some f
    | f :: fl => match (t_and_l fl) with
                | Some fl' => t_and f fl'
                | None => None
                end
    end.

