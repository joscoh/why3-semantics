Require Import Wstdlib.
Require Import Ident.
Require Number.
Require Import stdpp.base.
Require Import Coq.Wellfounded.Inverse_Image.

Record tvsymbol := {
  tv_name : ident
}.

Definition tvsymbol_eqb (t1 t2: tvsymbol) : bool :=
  ident_eqb t1.(tv_name) t2.(tv_name).

Lemma tvsymbol_eqb_eq (t1 t2: tvsymbol): t1 = t2 <-> tvsymbol_eqb t1 t2.
Proof.
  unfold tvsymbol_eqb.
  rewrite <- ident_eqb_eq.
  destruct t1 as [t1]; destruct t2 as [t2]; simpl;
  split; intros Heq; inversion Heq; subst; reflexivity.
Qed.

Definition tvsymbol_eq : base.EqDecision tvsymbol :=
  dec_from_eqb _ tvsymbol_eqb_eq.

Module TvarTagged <: TaggedType.
Definition t := tvsymbol.
Definition tag tv := tv.(tv_name).(id_tag).
Definition eq := tvsymbol_eq.

End TvarTagged.

Module Tvar := MakeMSH TvarTagged.
Module Stv := Tvar.S.
Module Mtv := Tvar.M.
(*Module Htv := Tvar.H*)

(*== in OCaml*)
Definition tv_equal (t1 t2: tvsymbol) : bool := tvsymbol_eqb t1 t2.
Definition tv_hash tv := id_hash tv.(tv_name).
(*Skip tv_compare*)

(*Not stateful, unlike OCaml*)
Definition create_tvsymbol (n: preid) : ctr tvsymbol :=
  i ← id_register n;
  ctr_ret {| tv_name := i|}.

(*In OCaml, this is a stateful function that stores variables
  in hash table and looks up to see if any have been
  created with same name already.
  Here, we just give a new one - NOTE: is this a problem?*)
Definition tv_of_string (s: string) : ctr tvsymbol :=
  create_tvsymbol (id_fresh s).

(** Type Symbols and Types **)
(*For Now*)
Unset Elimination Schemes.

Record ty_caml (A: Type) := 
  { ty_node: A;
    ty_tag: CoqBigInt.t}.

Inductive type_def_caml (A: Type) : Type :=
  | NoDef_caml
  | Alias_caml: A -> type_def_caml A
  | Range_caml: Number.int_range -> type_def_caml A
  | Float_caml: Number.float_format -> type_def_caml A.
    
Record tysymbol_caml (A: Type) := {
  ts_name : ident;
  ts_args : list tvsymbol;
  ts_def : type_def_caml A
}.

Inductive type_def : Type :=
  | NoDef
  | Alias : ty -> type_def
  | Range: Number.int_range -> type_def
  | Float: Number.float_format -> type_def
with ty : Type :=
  | mk_ty : ty_node_ -> CoqBigInt.t -> ty
with tysymbol : Type :=
  | mk_ts : ident -> list tvsymbol -> type_def -> tysymbol
with ty_node_ : Type :=
  | Tyvar : tvsymbol -> ty_node_
  | Tyapp: tysymbol -> list ty -> ty_node_.

(*IMPORTANT: ONLY use these functions so we can extract*)
Definition node_of_ty (t: ty) : ty_node_ :=
  match t with
  | mk_ty n _ => n
  end.

Definition tag_of_ty (t: ty) : CoqBigInt.t :=
  match t with
  | mk_ty _ n => n
  end.

Definition ident_of_tysym (t: tysymbol) : ident :=
  match t with
  | mk_ts t _ _ => t
  end.

Definition vars_of_tysym (t: tysymbol) : list tvsymbol :=
  match t with
  | mk_ts _ t _ => t
  end.

Definition type_def_of_tysym (t: tysymbol) : type_def :=
  match t with
  | mk_ts _ _ t => t
  end.



(*Test with equality on ty*)
Fixpoint ty_eqb (t1 t2: ty) : bool :=
  CoqBigInt.eq (tag_of_ty t1) (tag_of_ty t2) &&
  ty_node_eqb (node_of_ty t1) (node_of_ty t2)
with ty_node_eqb (t1 t2: ty_node_) : bool :=
  match t1, t2 with
  | Tyvar v1, Tyvar v2 => tvsymbol_eqb v1 v2
  | Tyapp ts1 tys1, Tyapp ts2 tys2 =>
    tysymbol_eqb ts1 ts2 &&
    ((fix tys_eqb (l1 l2: list ty) : bool :=
      match l1, l2 with
      | h1 :: t1, h2 :: t2 => ty_eqb h1 h2 && tys_eqb t1 t2
      | nil,nil => true
      | _, _ => false
      end) tys1 tys2)
  | _, _ => false
  end
with tysymbol_eqb (t1 t2: tysymbol) : bool :=
  ident_eqb (ident_of_tysym t1) (ident_of_tysym t2) &&
  list_eqb tvsymbol_eqb (vars_of_tysym t1) (vars_of_tysym t2) &&
  match type_def_of_tysym t1, type_def_of_tysym t2 with
  | NoDef, Nodef => true
  | Alias a1, Alias a2 => ty_eqb a1 a2
  | Range n1, Range n2 => Number.int_range_eqb n1 n2
  | Float f1, Float f2 => Number.float_format_eqb f1 f2
  | _, _ => false
  end.


(*Arguments ty_rec {A}.
Arguments ty_node {A}.
Arguments ty_tag {A}.*)



(*Arguments tysymbol_ {A}.
Arguments ts_name {A}.
Arguments ts_args {A}.
Arguments ts_def {A}.

Inductive ty_node__ : Type :=
  | Tyvar_ : tvsymbol -> ty_node__
  | Tyapp_ : @tysymbol_ ty_node__ -> list (@ty_ ty_node__) -> ty_node__.
*)
(*Definition ty' := @ty_ ty_node__.

Definition tysymbol' := @tysymbol_ ty_node__.*)




(*Try again*)
(*

(*This is surprisingly difficult to deal with, because 
  Coq does not support mixed Record and Inductive mutually
  recursive types (why3 uses these extensively).
  We want to mantain compatibility with the API, as external
  clients like Frama-C do in fact use record notation on these
  values. 
  There is a way to encode this by making the recursive argument
  polymorphic and instantiating it later with itself.
  This results in the OCaml types we expect, at the cost of
  being able to write Fixpoint functions, since Coq can no
  longer tell such definitions are well-founded.
  We can fix this by defining a size metric and doing
  well-founded recursion (as in Well-Founded Recursion
  Done Right). But this is painful to do for every function,
  and generic functions (say, an induction principle)*)

Inductive type_def (A: Type) : Type :=
  | NoDef
  | Alias: A -> type_def A
  | Range: Number.int_range -> type_def A
  | Float: Number.float_format -> type_def A.

(*We do this to get around the restriction that
  Coq Records and Inductives cannot be mutually recursive
  with each other. TODO: see if we can ensure that
  this satisfies the correct .mli file*)
Record ty_ (A: Type) := 
  { ty_node: A;
    ty_tag: CoqBigInt.t}.

Arguments ty_ {A}.
Arguments ty_node {A}.
Arguments ty_tag {A}.

Record tysymbol_ (A: Type) := {
  ts_name : ident;
  ts_args : list tvsymbol;
  ts_def : type_def (@ty_ A)
}.

Arguments tysymbol_ {A}.
Arguments ts_name {A}.
Arguments ts_args {A}.
Arguments ts_def {A}.

Inductive ty_node_ : Type :=
  | Tyvar : tvsymbol -> ty_node_
  | Tyapp : @tysymbol_ ty_node_ -> list (@ty_ ty_node_) -> ty_node_.

Definition ty := @ty_ ty_node_.

Definition tysymbol := @tysymbol_ ty_node_.

(*This encoding satisfies the expected OCaml interface
  (with a mixed record-inductive type), but because Coq
  does not allow us to write this directly, we do not
  have a good induction principle. While we could
  (and TODO maybe will) prove an induction principle,
  we instead give a simpler construction for writing
  the kinds of functions we will need: those that
  take a [ty] and match on the [ty_node].
  First, we need well-foundedness, so we define a size*)
Section TyFuncs.

Section TySize.


(*TODO: try with Xavier trick (Equations bad extraction I think) and manual rec*)
(*Define size*)
Fixpoint ty_node_size (t: ty_node_) : nat :=
  match t with
  | Tyvar v => 1
  | Tyapp ts tys => 1 +
    (*tysymbol size*)
    (1 + match (ts_def ts) with
          | NoDef _ => 0
          | Alias _ x => 1 + (1 + ty_node_size (x.(ty_node)))
          | _=> 1
    end) +
  
   list_sum 
      (map (fun (x: ty) => 1 + ty_node_size (x.(ty_node))) tys)
  end.

Definition ty_size (t: ty) : nat :=
  1 + ty_node_size (t.(ty_node)).

Definition tysymbol_size (ts: tysymbol) : nat :=
  1 + match ts_def ts with
    | NoDef _ => 0
    | Alias _ x => 1 + ty_size x
    | _ => 1
  end.

Lemma ty_node_size_rewrite (t: ty_node_) :
  ty_node_size t =
  match t with
  | Tyvar v => 1
  | Tyapp ts tys => 1 + tysymbol_size ts + 
    list_sum (map ty_size tys)
  end.
Proof.
  destruct t; simpl; auto.
Qed.

Definition ty_size_rel (t1 t2: ty) : Prop :=
  ty_size t1 < ty_size t2.

Lemma ty_size_rel_wf: well_founded ty_size_rel.
Proof.
  unfold well_founded. intros.
  unfold ty_size_rel.
  apply Inverse_Image.Acc_inverse_image.
  apply lt_wf.
Qed.

Definition ty_node_size_rel (t1 t2: ty) : Prop :=
  ty_node_size (t1.(ty_node)) < ty_node_size (t2.(ty_node)).

Lemma ty_node_size_rel_wf: well_founded ty_node_size_rel.
Proof.
  unfold well_founded. intros.
  unfold ty_node_size_rel.
  apply Inverse_Image.Acc_inverse_image.
  apply lt_wf.
Qed.

End TySize.

(*Obligations for function def:*)

Lemma node_lt_ty (t: ty):
  ty_node_size (ty_node t) < ty_size t.
Proof.
  unfold ty_size. lia.
Qed.

Lemma in_tys_lt_app {t ts tys}:
  ty_node_size (Tyapp ts tys) < ty_size t ->
  Forall (fun x => ty_size_rel x t) tys.
Proof.
  rewrite ty_node_size_rewrite. intros.
  intros.
  rewrite List.Forall_forall; intros x Hinx.
  unfold ty_size_rel.
  pose proof (in_split x tys Hinx) as Hsplit.
  destruct Hsplit as [l1 [l2 Htys]]; subst.
  revert H.
  rewrite map_app. simpl map.
  rewrite list_sum_app. simpl list_sum.
  intros.
  unfold ty_size at 1. lia.
Qed.

Section TyBuildSimpl.

Variable (A: Type)(B: Type).

Variable (Hvar: tvsymbol -> A).
Variable (Happ: tysymbol -> list ty -> B -> A).

Variable (base: B).
Variable (combine: A -> B -> B).

Fixpoint ty_build_simpl' (t: ty) (ACC: Acc ty_size_rel t) {struct ACC} : A :=
  match t.(ty_node) as n return ty_node_size n < ty_size t -> A with
  | Tyvar v => fun _ => Hvar v
  | Tyapp ts tys => fun Hlt => Happ ts tys
    ((fix tys_fold (l: list ty) (Hall: Forall (fun x => ty_size_rel x t) l) : B :=
      match l as l' return Forall (fun x => ty_size_rel x t) l' -> B with
      | nil => fun _ => base
      | x :: xs => fun Hall => 
        combine (ty_build_simpl' x (Acc_inv ACC _ (Forall_inv Hall))) 
        (tys_fold xs (Forall_inv_tail Hall))
      end Hall) tys (in_tys_lt_app  Hlt))
  end (node_lt_ty t).

Definition ty_build_simpl t := ty_build_simpl' t (ty_size_rel_wf t).

(*One theorem we need for using this:*)

Lemma ty_size_rel_node_rel (t1 t2: ty):
  ty_size_rel t1 t2 <-> ty_node_size_rel t1 t2.
Proof.
  unfold ty_size_rel, ty_size, ty_node_size_rel. lia.
Qed.

Lemma ty_build_simpl_irrel t ACC1 ACC2:
  ty_build_simpl' t ACC1 = ty_build_simpl' t ACC2.
Proof.
  induction t using (well_founded_induction ty_node_size_rel_wf).
  destruct ACC1; destruct ACC2.
  simpl.
  destruct t as [n tg]; simpl. destruct n; auto.
  f_equal.
  generalize dependent (in_tys_lt_app (node_lt_ty {| ty_node := Tyapp t l; ty_tag := tg |})).
  generalize dependent {| ty_node := Tyapp t l; ty_tag := tg |}.
  induction l; simpl; auto.
  intros. erewrite IHl. f_equal.
  apply H.
  inversion f; subst.
  apply ty_size_rel_node_rel. auto.
  auto.
Qed.

(*And the rewrite lemma:*)
Lemma ty_build_simpl_rewrite (t: ty) :
  ty_build_simpl t =
  match t.(ty_node) with
        | Tyvar v => Hvar v
        | Tyapp ts tys => Happ ts tys 
            (fold_right (fun x acc => combine (ty_build_simpl x) acc) base tys)
  end.
Proof.
  unfold ty_build_simpl at 1.
  generalize dependent (ty_size_rel_wf t).
  intros a. destruct a.
  destruct t as [n tg].
  destruct n; [reflexivity |].
  simpl. f_equal.
  (*Problem: have l in Forall*)
  generalize dependent (in_tys_lt_app (node_lt_ty {| ty_node := Tyapp t l; ty_tag := tg |})).
  generalize dependent {| ty_node := Tyapp t l; ty_tag := tg |}.
  intros t' a'.
  induction l; simpl; auto.
  intros.
  rewrite IHl.
  f_equal.
  apply ty_build_simpl_irrel.
Qed.

End TyBuildSimpl.

(*More general functions*)

(*Do same with Type so that we can write functions and test extraction*)

Definition type_def_p_ty (P: ty -> Type) (t: type_def ty_) : Type :=
  match t with
  | Alias _ x => P x
  | _ => True
  end.


Inductive ForallT {A: Type} (P: A -> Type) : list A -> Type :=
  | ForallT_nil: ForallT P nil
  | ForallT_cons: forall {x: A} {l: list A},
    P x -> ForallT P l -> ForallT P (x :: l).

Lemma ForallT_hd {A: Type} (P: A -> Type) (x: A) (l: list A):
  ForallT P (x :: l) ->
  P x.
Proof.
  intros. inversion X; subst. apply X0.
Qed.

Lemma ForallT_tl {A: Type} (P: A -> Type) (x: A) (l: list A):
  ForallT P (x :: l) ->
  ForallT P l.
Proof.
  intros. inversion X; auto.
Qed.

Lemma ForallT_In {A: Type} (P: A -> Type)
  (eq_dec: forall (x y: A), {x = y} + {x <> y}) (l: list A):
  ForallT P l ->
  forall x, In x l -> P x.
Proof.
  intros Hall. induction Hall; simpl; intros.
  destruct H.
  destruct (eq_dec x x0); subst; auto.
  apply IHHall. destruct H; subst; auto.
  contradiction.
Qed.

Lemma typesym_lt_node (ts: tysymbol) (tys: list ty):
  tysymbol_size ts < ty_node_size (Tyapp ts tys).
Proof.
  rewrite ty_node_size_rewrite.
  lia.
Qed.


Section TyRect.

Variable (P: ty -> Type).
Variable (P1: ty_node_ -> Type).
Variable (P2: tysymbol -> Type).

Variable (Hty: forall (t: ty), P1 (t.(ty_node)) -> P t).
Variable (Hsym: forall (ts: tysymbol), type_def_p_ty P (ts.(ts_def)) ->
  P2 ts).
Variable (Hvar: forall v, P1 (Tyvar v)).
Variable (Happ: forall ts tys, P2 ts -> ForallT P tys -> P1 (Tyapp ts tys)).

(*This does NOT work - tysymbol is not recursive so we can't have
  a fixpoint on it
  Maybe could do same trick (assume we have proof, populate later)
  but likely to run into positivity problems*)


(*Fixpoint gcd_rec (a b: nat) (ACC: Acc lt b) {struct ACC} : nat :=
  if Nat.eq_dec b 0 then a else gcd_rec b (a mod b) (Acc_inv ACC _).*)

(*TODO: need decomposition if we want idiomatic code, maybe need eq_rect*)
(*Plan: prove lemmas, do in Set, test extraction (without Program) *)
Fixpoint ty_rect' (t: ty) (ACC: Acc lt (ty_size t)) {struct ACC} : P t :=
  (Hty t (ty_node_rect' t.(ty_node) 
    (Acc_inv ACC (ty_node_size (ty_node t)) (node_lt_ty t))))
with ty_node_rect' (t: ty_node_) (ACC: Acc lt (ty_node_size t)) {struct ACC} : P1 t :=
  match t as t' return Acc lt (ty_node_size t') -> P1 t' with
  | Tyvar tv => fun _ => Hvar tv
  | Tyapp ts tys => fun ACC => Happ ts tys (tysymbol_rect' ts (Acc_inv ACC (tysymbol_size ts) 
      (typesym_lt_node ts tys))) 
    ((fix tys_rect (l: list ty) 
      (Hl: Forall (fun x => ty_size x < (ty_node_size (Tyapp ts tys))) l) 
      : ForallT P l :=
      match l as l' return Forall  (fun x => ty_size x < (ty_node_size (Tyapp ts tys))) l'->
        ForallT P l'  with
      | nil => fun _ => ForallT_nil _
      | x :: xs => fun Hl => ForallT_cons _ (ty_rect' x (Acc_inv ACC (ty_size x) 
        (List.Forall_inv Hl))) 
        (tys_rect xs (List.Forall_inv_tail Hl))
      end Hl) tys (in_tys_lt_app ts tys))
  end ACC
with tysymbol_rect' (ts: tysymbol) (ACC: Acc lt (tysymbol_size ts)) {struct ACC} : P2 ts :=
  Hsym ts (
    match (ts.(ts_def)) as d' return type_def_size d' < tysymbol_size ts -> 
       type_def_p_ty P d' with
    | NoDef _ => fun _ => I
    | Alias _ x => fun Hlt => ty_rect' x (Acc_inv ACC (ty_size x) (alias_lt_sym Hlt))
    end (def_lt_sym ts)
  ).

Definition ty_rect (t: ty) : P t := ty_rect' t (lt_wf _).
Definition ty_node_rect (t: ty_node_) : P1 t := ty_node_rect' t (lt_wf _).
Definition tysymbol_rect (ts: tysymbol) : P2 ts := tysymbol_rect' ts (lt_wf _).

End TyRect.

(*Example (TODO move)*)
Definition ty_v_map (f: tvsymbol -> ty) (t: ty) : ty :=
  ty_build_simpl ty (list ty) (fun v => f v)
  (fun ts tys res => Build_ty_ _ (Tyapp ts res) CoqBigInt.zero) 
  nil cons t.
Print type_def.

(*For equality, we have to do things manually*)
Fixpoint ty_eqb (t1 t2: ty) (ACC: Acc ty_size_rel t1) {struct ACC} :=
  ty_node_eqb t1.(ty_node) t2.(ty_node) &&
  CoqBigInt.eq t1.(ty_tag) t2.(ty_tag) 
with ty_node_eqb (t1 t2: ty_node) (ACC: Acc ty_node_size_rel t1) {struct ACC} :=
  match t1, t2 with
  | Tyvar v1, Tyvar v2 => tvsymbol_eqb v1 v2
  | Tyapp ts1 tys1, Tyapp ts2 tys2 =>
    tysymbol_eqb ts1 ts2 &&
    ((fix tys_eqb (l1 l2: list ty) : bool :=
      match l1, l2 with
      | h1 :: tl1, h2 :: tl2 => ty_eqb h1 h2 && tys_eqb tl1 tl2
      | nil, nil => true
      | _, _ => false
      end) tys1 tys2)
  | _, _ => false
  end
with tysymbol_eqb (ts1 ts2: tysymbol) (ACC: Acc tysymbol_size_rel t1) {struct ACC} :=
  ident_eqb t1.(ts_name) t2.(ts_name) &&
  list_eqb tvsymbol_eqb t1.(ts_args) t2.(ts_args) &&




Record ty_ (A: Type) := 
  { ty_node: A;
    ty_tag: CoqBigInt.t}.



Fixpoint ty_build_simpl' (t: ty) (ACC: Acc ty_size_rel t) {struct ACC} : A :=
  match t.(ty_node) as n return ty_node_size n < ty_size t -> A with
  | Tyvar v => fun _ => Hvar v
  | Tyapp ts tys => fun Hlt => Happ ts tys
    ((fix tys_fold (l: list ty) (Hall: Forall (fun x => ty_size_rel x t) l) : B :=
      match l as l' return Forall (fun x => ty_size_rel x t) l' -> B with
      | nil => fun _ => base
      | x :: xs => fun Hall => 
        combine (ty_build_simpl' x (Acc_inv ACC _ (Forall_inv Hall))) 
        (tys_fold xs (Forall_inv_tail Hall))
      end Hall) tys (in_tys_lt_app  Hlt))
  end (node_lt_ty t).


(*This almost works, but not quite, because our function
  schema is not specific enough*)
(*Definition ty_eqb (t1 t2: ty) : bool :=
  (ty_build_simpl (ty -> bool) (list ty -> bool) (fun v t2 => 
    match t2.(ty_node) with
    | Tyvar v2 => typevar_eqb v v2
    | _ => false
    end) 
    (fun ts tys res t2 => match t2.(ty_node) with
    | Tyapp ts1 tys2 => tysymbol_eqb ts ts1 &&
      res tys2
    | _ => false
    end) 
    (*Base*)
    (fun l =>
      match l with 
      | nil => true
      | _ => false
      end)
    (*combine*)
    (fun fhd ftl =>
      fun l => match l with
                | hd1 :: tl1 => fhd hd1 && ftl tl1
                | _ => false
      end)) t1 t2.*)
From Equations Require Import Equations.
Section TestEq.

Variable (f: tvsymbol -> ty).
(*Let's try with Equations and see how the resulting OCaml code is*)
Equations ty_v_map' (t: ty) : ty by
  struct t
  (*wf (ty_size t) lt*) :=
  ty_v_map' t := ty_v_map_node t.(ty_node)
where ty_v_map_node (t: ty_node_) : ty by
  struct t
  (*wf (ty_node_size t) lt*) :=
  ty_v_map_node (Tyvar v) := f v;
  ty_v_map_node (Tyapp ts tys) :=
    Build_ty_ _ (Tyapp ts (List.map (ty_v_map') tys)) xH.


    ty_app f (List.map (ty_v_map fn) tl)


  (list ty) (fun v => f v)
  (fun ts tys res => Build_ty_ _ (Tyapp ts res) xH) 
  nil cons t.



ty_v_map (f: tvsymbol -> ty) (t: ty) : ty :=
  ty_build_simpl ty (list ty) (fun v => f v)
  (fun ts tys res => Build_ty_ _ (Tyapp ts res) xH) 
  nil cons t.
    
    ) (fun )


  (fun ts tys res => res)

(*Now let's try a 2-argument one, of the form:
  let rec foo (t1 t2: ty) =
  match t1.ty_node, t2.ty_node with
  | Tyvar v1, Tyvar v2 => f1 v1 v2
  | Tyapp ts1 tys1, Tyapp ts2 tys2 => f2 ts1 tys1 ts2 tys2
  *)


(*Writing functions on types*)

(*Decidable equality on types*)



(*TODO: not best way*)
(*
Module Type Ty (I: Ident).

(*Type variables*)
Record tvsymbol := {
  tv_name : I.ident
}.

(*TODO: add range and float*)
Inductive type_def (A: Set) : Set :=
  | NoDef
  | Alias: A -> type_def A.

(*Fail Inductive tysymbol := {
  ts_name : I.ident;
  ts_args : list tvsymbol;
  ts_def: type_def ty
}
with ty := {
  ty_node : ty_node;
  ty_tag : tag
}
with ty_node_ :=
  | Tyvar : tvsymbol -> ty_node_
  | Tyapp : tysymbol -> list ty -> ty_node_.*)


(*1 version:
*)
Inductive tysymbol : Set :=
  | mk_tysymbol : I.ident -> list tvsymbol -> type_def ty -> tysymbol 
with ty : Set :=
  | mk_ty : ty_node_ -> tag -> ty
with ty_node_ : Set :=
  | Tyvar : tvsymbol -> ty_node_
  | Tyapp : tysymbol -> list ty -> ty_node_.


(*Simulate record but not as good*)
Parameter ts_name : tysymbol -> I.ident.
Parameter ts_args : tysymbol -> list tvsymbol.
Parameter ts_def : tysymbol -> type_def ty.

Parameter ty_node: ty -> ty_node_.
Parameter ty_tag: ty -> tag.

(*A few examples*)
Parameter ts_equal: tysymbol -> tysymbol -> bool.
(*Parameter ty_equal: ty -> ty -> bool.*)

End Ty.

Module TyImpl (I: Ident) <: Ty I.*)

(*Type variables*)
Record tvsymbol := {
  tv_name : ident
}.



(*Unset Elimination Schemes.
Inductive tysymbol : Set :=
  | mk_tysymbol : ident -> list tvsymbol -> type_def ty -> tysymbol 
with ty : Set :=
  | mk_ty : ty_node_ -> tag -> ty
with ty_node_ : Set :=
  | Tyvar : tvsymbol -> ty_node_
  | Tyapp : tysymbol -> list ty -> ty_node_.
Set Elimination Schemes.

Scheme tysymbol_ind := Induction for tysymbol Sort Prop with
ty_ind := Induction for ty Sort Prop with
ty_node__ind := Induction for ty_node_ Sort Prop.

Check ty_ind.*)




(*Test*)

(*This awkward definition satisfies Coq's positivity checker
  for nested induction, unlike the normal one*)
Definition map2 {A B C: Type} :=
  fun (f: A -> B -> C) =>
    fix map2 (l1: list A) : list B -> list C :=
      match l1 with
      | nil => fun l2 => nil
      | x1 :: t1 =>
        fun l2 =>
        match l2 with
        | nil => nil
        | x2 :: t2 => f x1 x2 :: map2 t1 t2
        end
      end.

(*This doesn't work, let's try to prove induction principle*)
Fail Fixpoint ty_equal (t1 t2: ty) {struct t1} : bool :=
  match t1.(ty_node), t2.(ty_node) with
  | Tyvar v1, Tyvar v2 => true
  | Tyapp ts1 tys1, Tyapp ts2 tys2 => 
    forallb (fun x => x) (map2 ty_equal tys1 tys2)
  | _, _ => false
  end.


Definition type_def_p (P: ty -> Prop) (t: type_def ty_) : Prop :=
  match t with
  | NoDef _ => True
  | Alias _ x => P x
  end.

Section TyInd.

Variable (P: ty -> Prop).
Variable (P1: ty_node_ -> Prop).
Variable (P2: tysymbol -> Prop).

Variable (Hty: forall n t, P1 n -> P (Build_ty_ _ n t)).
Variable (Hsym: forall n vs t, type_def_p P t -> P2 (Build_tysymbol_ _ n vs t)).
Variable (Hvar: forall v, P1 (Tyvar v)).
Variable (Happ: forall ts tys, P2 ts -> Forall P tys -> P1 (Tyapp ts tys)).

(*This does NOT work - tysymbol is not recursive so we can't have
  a fixpoint on it
  Maybe could do same trick (assume we have proof, populate later)
  but likely to run into positivity problems*)

Fail Fixpoint ty_ind (t: ty) : P t :=
  match t with
  | Build_ty_ _ n tg => Hty n tg (ty_node_ind n)
  end
with ty_node_ind (t: ty_node_) : P1 t :=
  match t with
  | Tyvar tv => Hvar tv
  | Tyapp ts tys => Happ ts tys (tysymbol_ind ts) 
    ((fix tys_ind (l: list ty) : Forall P l :=
      match l with
      | nil => List.Forall_nil _
      | x :: xs => List.Forall_cons _ _ _ (ty_ind x) (tys_ind xs)
      end) tys)
  end
with tysymbol_ind (ts: tysymbol) : P2 ts :=
  match ts with
  | Build_tysymbol_ _ n l d => Hsym n l d 
    (match d as d' return type_def_p P d' with
      | NoDef _ => I
      | Alias _ x => ty_ind x
    end)
  end.

End TyInd.

(*Let's try bad*)
Inductive func {A: Set} : Set :=
  | func1: (A -> A) -> func.

Fail Inductive bad : Set :=
  | bad1: @func bad -> bad.

(*Next: structural recursion on size*)


(*Need version of map2 with in*)
Definition map2' {A B C: Type} :=
    fix map2 (l1: list A) : list B -> (A -> B -> C) -> list C :=
      match l1 with
      | nil => fun l2 f => nil
      | x1 :: t1 =>
        fun l2 f =>
        match l2 with
        | nil => nil
        | x2 :: t2 => f x1 x2 :: map2 t1 t2 f
        end
      end.

Definition map2'' {A B C: Type} :=
    fix map2 (l1: list A) : forall (l2: list B), 
      (forall (x: A) (Hinx: In x l1) (y: B) (Hiny: In y l2), C) -> list C :=
      match l1 with
      | nil => fun l2 f => nil
      | x1 :: t1 =>
        fun l2 =>
        match l2 with
        | nil => fun f => nil
        | x2 :: t2 => fun f => f x1 (in_eq _ _) x2 (in_eq _ _) :: map2 t1 t2 
          (fun x Hin y Hin2 => f x (in_cons _ _ _ Hin) y (in_cons _ _ _ Hin2))
        end
      end.

Definition type_def_size (t: type_def ty) : nat :=
  match t with
  | NoDef _ => 0
  | Alias _ x => 1 + ty_size x
  end.


(*Obligations (do here to test OCaml)*)


Lemma ty_decomp (t: ty):
{| ty_node := ty_node t; ty_tag := ty_tag t |} = t.
Proof.
  destruct t; reflexivity.
Qed.


(*Lemma foo (x: nat) x < x + 1.

Lemma bar (x y: nat) : x < y -> y > x.*)

Lemma in_tys_lt_app (ts: tysymbol) (tys: list ty) :
Forall (fun x : ty => ty_size x < ty_node_size (Tyapp ts tys)) tys.
Proof.
  (*TODO: bad proof*)
  rewrite ty_node_size_rewrite.
  rewrite List.Forall_forall; intros x Hinx.
  pose proof (in_split x tys Hinx) as Hsplit.
  destruct Hsplit as [l1 [l2 Htys]]; subst.
  rewrite map_app; simpl.
  rewrite list_sum_app. simpl. unfold ty_size at 1. lia.
Qed.

Lemma alias_lt_sym {x ts}:
type_def_size (Alias ty_ x) < tysymbol_size ts ->
ty_size x < tysymbol_size ts.
Proof.
  simpl. lia.
Qed.

Lemma def_lt_sym ts: type_def_size (ts_def ts) < tysymbol_size ts.
Proof.
  unfold tysymbol_size; simpl.
  destruct (ts_def ts); auto.
Qed.

(*Let's try to prove an induction principle*)

Section TyInd.

Variable (P: ty -> Prop).
Variable (P1: ty_node_ -> Prop).
Variable (P2: tysymbol -> Prop).

Variable (Hty: forall (t: ty), P1 (t.(ty_node)) -> P t).
Variable (Hsym: forall (ts: tysymbol), type_def_p P (ts.(ts_def)) ->
  P2 ts).
Variable (Hvar: forall v, P1 (Tyvar v)).
Variable (Happ: forall ts tys, P2 ts -> Forall P tys -> P1 (Tyapp ts tys)).

(*This does NOT work - tysymbol is not recursive so we can't have
  a fixpoint on it
  Maybe could do same trick (assume we have proof, populate later)
  but likely to run into positivity problems*)


(*Fixpoint gcd_rec (a b: nat) (ACC: Acc lt b) {struct ACC} : nat :=
  if Nat.eq_dec b 0 then a else gcd_rec b (a mod b) (Acc_inv ACC _).*)

(*TODO: need decomposition if we want idiomatic code, maybe need eq_rect*)
(*Plan: prove lemmas, do in Set, test extraction (without Program) *)
Fixpoint ty_ind' (t: ty) (ACC: Acc lt (ty_size t)) {struct ACC} : P t :=
  (Hty t (ty_node_ind' t.(ty_node) 
    (Acc_inv ACC (ty_node_size (ty_node t)) (node_lt_ty t))))
with ty_node_ind' (t: ty_node_) (ACC: Acc lt (ty_node_size t)) {struct ACC} : P1 t :=
  match t as t' return Acc lt (ty_node_size t') -> P1 t' with
  | Tyvar tv => fun _ => Hvar tv
  | Tyapp ts tys => fun ACC => Happ ts tys (tysymbol_ind' ts (Acc_inv ACC (tysymbol_size ts) 
      (typesym_lt_node ts tys))) 
    ((fix tys_ind (l: list ty) 
      (Hl: Forall (fun x => ty_size x < (ty_node_size (Tyapp ts tys))) l) 
      : Forall P l :=
      match l as l' return Forall  (fun x => ty_size x < (ty_node_size (Tyapp ts tys))) l'->
        Forall P l'  with
      | nil => fun _ => List.Forall_nil _
      | x :: xs => fun Hl => List.Forall_cons _ _ _ (ty_ind' x (Acc_inv ACC (ty_size x) 
        (List.Forall_inv Hl))) 
        (tys_ind xs (List.Forall_inv_tail Hl))
      end Hl) tys (in_tys_lt_app ts tys))
  end ACC
with tysymbol_ind' (ts: tysymbol) (ACC: Acc lt (tysymbol_size ts)) {struct ACC} : P2 ts :=
  Hsym ts (
    match (ts.(ts_def)) as d' return type_def_size d' < tysymbol_size ts -> 
       type_def_p P d' with
    | NoDef _ => fun _ => I
    | Alias _ x => fun Hlt => ty_ind' x (Acc_inv ACC (ty_size x) (alias_lt_sym Hlt))
    end (def_lt_sym ts)
  ).

Definition ty_ind (t: ty) : P t := ty_ind' t (lt_wf _).
Definition ty_node_ind (t: ty_node_) : P1 t := ty_node_ind' t (lt_wf _).
Definition tysymbol_ind (ts: tysymbol) : P2 ts := tysymbol_ind' ts (lt_wf _).

End TyInd.




(*Alternate version, more useful*)
Section TyBuild.

(*First is for ty, second is for ty_node_*)
Variable (A: Type) (B: Type) (C: Type).

(*type, result of calling function on t.ty_node, result*)
Variable (Hty: ty -> B -> A).
Variable (Hvar: tvsymbol -> B).
(*TODO: not general enough probably*)
(*3rd param: folding over the resulting list*)
Variable (base: C).
Variable (combine: C -> A -> C).
(*B is result of fold over list of tys*)
Variable (Happ: tysymbol -> list ty -> C -> B).

Fixpoint ty_build' (t: ty) (ACC: Acc lt (ty_size t)) {struct ACC} : A :=
  (Hty t (ty_node_build' t.(ty_node)
    (Acc_inv ACC (ty_node_size (ty_node t)) (node_lt_ty t))))
with ty_node_build' (t: ty_node_) (ACC: Acc lt (ty_node_size t)) {struct ACC} : B :=
  match t as t' return Acc lt (ty_node_size t') -> B with
  | Tyvar tv => fun _ => Hvar tv
  | Tyapp ts tys => fun ACC => Happ ts tys
    (*Here, we implement fold*)
    ((fix tys_fold (l: list ty) 
      (Hl: Forall (fun x => ty_size x < (ty_node_size (Tyapp ts tys))) l) 
      : C :=
      match l as l' return Forall  (fun x => ty_size x < (ty_node_size (Tyapp ts tys))) l'->
        C  with
      | nil => fun _ => base
      | x :: xs => fun Hl => combine (tys_fold xs (List.Forall_inv_tail Hl))
          (ty_build' x (Acc_inv ACC (ty_size x) 
        (List.Forall_inv Hl)))
      end Hl) tys (in_tys_lt_app ts tys))
  end ACC.

Definition ty_build (t: ty) := ty_build' t (lt_wf _).
Definition ty_node_build (t: ty_node_) := ty_node_build' t (lt_wf _).


End TyBuild.


  


(*TODO: prove this later*)
(*Ltac hide_right := match goal with |- _ = ?rhs =>remember rhs end. 

Lemma ty_build_rewrite (t: ty):
  ty_build t =
  Hty t (match t.(ty_node) with
        | Tyvar v => Hvar v
        | Tyapp ts tys => Happ ts tys 
            (fold_right (fun x acc => combine acc (ty_build x)) base tys)
  end).
Proof.
  unfold ty_build.
  destruct (lt_wf (ty_size t)) as [a].
  simpl ty_build' at 1. f_equal.
  generalize dependent (a (ty_node_size (ty_node t)) (node_lt_ty t)).
  intros a1.
  destruct a1. 
  

  
   unfold ty_node_build'. cbv beta. cbv. simpl ty_node_build' at 1.
  destruct t as [n tg].
  destruct n.
  - simpl; auto.
  - hide_right. simpl. subst b.
    simpl ty_node. cbv iota. f_equal.
    generalize dependent (in_tys_lt_app t l).
    induction l; auto.
    intros Hall. (*TODO: bad hack*) Opaque ty_build'. simpl.
    f_equal.
    erewrite <- IHl.

    Unshelve. reflexivity.
    f_equal.


    + auto.
    + simpl. auto.




  
  
   simpl ty_node_build' at 1.
  destruct t as [n tg].
  simpl ty_node at 1 2 .
  simpl.


  (*To generalize*)
  assert (forall (f: forall x : ty_, Acc lt (ty_node_size (ty_node x))),
    Hty t (ty_node_build' (ty_node t) (a (ty_node_size (ty_node t)) (node_lt_ty t))) =
    match ty_node t with
    | 




  generalize dependent (fun x => (Acc_intro (ty_node_size (ty_node x)) (λ (b : nat) (Hb : b < ty_node_size (ty_node x)), nat_ind (λ n : nat, ∀ a0 : nat, a0 < n → Acc (ltof nat (λ m : nat, m)) a0) (λ (a0 : nat) (Ha : a0 < 0), False_ind (Acc (ltof nat (λ m : nat, m)) a0) (PeanoNat.Nat.nlt_0_r a0 Ha)) (λ (n : nat) (IHn : ∀ a0 : nat, a0 < n → Acc (ltof nat (λ m : nat, m)) a0) (a0 : nat) (Ha : a0 < S n), Acc_intro a0 (λ (b0 : nat) (Hb0 : b0 < a0), IHn b0 (PeanoNat.Nat.lt_le_trans b0 a0 n Hb0 (match PeanoNat.Nat.succ_le_mono a0 n with
| conj _ H0 => H0
end Ha)))) (ty_node_size (ty_node x)) b (PeanoNat.Nat.lt_le_trans b (ty_node_size (ty_node x)) (ty_node_size (ty_node x)) Hb (match PeanoNat.Nat.succ_le_mono (ty_node_size (ty_node x)) (ty_node_size (ty_node x)) with
| conj _ H0 => H0
end (PeanoNat.Nat.lt_le_trans (ty_node_size (ty_node x)) (ty_size x) (ty_size x) (node_lt_ty x) (match PeanoNat.Nat.succ_le_mono (ty_size x) (ty_size x) with
| conj _ H0 => H0
end (PeanoNat.Nat.lt_succ_diag_r (ty_size x))))))))).


  generalize dependent 
  Check Acc_intro.
  match goal with
  | |- context [Acc_intro ?a ?b ?c ?d] => idtac a
  end.
  generalize dependent (a (ty_node_size (ty_node t)) (node_lt_ty t)).
  destruct t; simpl. intros a1. f_equal.
  destruct ty_node0; simpl.
  - destruct a1; auto.
  - destruct a1; simpl. f_equal.
  
  
   destruct (a 1 (node_lt_ty {| ty_node := Tyvar t; ty_tag := ty_tag0 |})); simpl; auto.
  - destruct ((a (S (S (match ts_def t with
| NoDef _ => 0
| Alias _ x => S (S (ty_node_size (ty_node x)))
end + list_sum (map (λ x : ty, S (ty_node_size (ty_node x))) l)))))).
  
   unfold ty_node_build'; simpl.

  (*generalize dependent (lt_wf (ty_size t)).*)
  induction t using (well_founded_induction (ty_size_rel_wf)).
  intros ACC.
  destruct t as [n tg].
  inversion ACC.
  unfold ty_build' at 1. simpl.
  simpl ty_build'. at 1.
  simpl at 1.
  destruct t; simpl in *.



  revert t.
  eapply ty_ind with (P1).
  - intros.

    destruct t0; simpl.
  
   with (P:= fun t => forall(a : Acc lt (ty_size t)), ty_build' t a = Hty t match ty_node t with
| Tyvar v => Hvar v
| Tyapp ts tys => Happ ts tys (foldr (λ (x : ty) (acc : C), combine acc (ty_build' x (lt_wf (ty_size x)))) base tys)
end ).

  dependent induction (ty_size t) using (well_founded_induction lt_wf).
  unfold ty_build'. simpl. 
        
        
        
        combine base tys))


End TyBuild.*)




(*
Definition ty_v_map (f: tvsymbol -> ty) (t: ty) :=
  ty_build ty (fun _ x => x) (fun v => f v) (fun ts tys IHl =>
    Build_ty_ _ (Tyapp ts IHl) xH).


Eval compute in 

(*Let us do ty_v_map first*)
Definition ty_v_map (f: tvsymbol -> ty) (t: ty) :=
  ty_rect (fun (_: ty) => ty) (fun (_: ty_node) => ty) (fun _ => unit)
  (*ty case*)
  (fun (t1: ty) (res: bool) => res)
  (fun _ _ => tt)
  (*Tvar*)
  (fun (v: tvsymbol) => f v)
  (*Tyapp*)
  (fun (ts: tysymbol) (tys: list ty) (IH))

(*Common pattern:
  let rec ty_foo (t1 t2: ty) : A :=
    match t1.ty_node, t2.ty_node with
    | *)

(*Test*)
Fixpoint list_eq (l1 l2: list nat) : bool :=
  match l1, l2 with
  | x1 :: t1, x2 :: t2 => Nat.eqb x1 x2 && list_eq t1 t2
  | nil, nil => true
  | _, _ => false
  end.

Definition list_eq' (l1 l2: list nat) : bool.
revert l2.
induction l1 as [| x1 t1 eq_t1]; intros l2.
- destruct l2.
  + apply true.
  + apply false.
- destruct l2 as [| x2 t2].
  + apply false.
  + apply (Nat.eqb x1 x2 && eq_t1 t2).
Defined.

Definition list_eq'' : list nat -> list nat -> bool :=
  (list_rec (fun (_ : list nat) => list nat -> bool)
    (*nil case*)
    (fun l2 => match l2 with
              | nil => true
              | _ => false
    end)
    (*cons case*)
    (fun x1 t1 (IH: list nat -> bool) (l2: list nat) =>
      match l2 with
      | nil => false
      | x2 :: t2 => Nat.eqb x1 x2 && IH t2
      end
    )).
(*NOTE: I think we DONT want ForallT, maybe want fixpoint instead but see*)
(*NOTE: want version without tysymbol*)
(*Now we can define an equality function (maybe)*)
Definition ty_equal (t1 t2: ty) : bool :=
  ty_rect (fun (_: ty) => ty -> bool ) (fun (_: ty_node_ ) => ty_node_ -> bool) 
    (fun _ => unit)
  (*ty case*)
  (fun (t1: ty) (node_eq: ty_node_ -> bool) (t2: ty) =>
    node_eq (t2.(ty_node))
  )
  (*tysymbol case*)
  (fun (ts1: tysymbol) _ => tt)
  (*ty_node_ Tyvar case*)
  (fun (v1: tvsymbol) (t2: ty_node_) =>
    match t2 with
    | Tyvar v2 => true (*TODO*)
    | _ => false
    end) 
  (*ty_node_ Tyapp case*)
  (fun (ts: tysymbol) (tys: list ty) (_: unit) IH (t2: ty_node_) =>
    match t2 with
    | Tyvar v2 => false
    | Tyapp ts2 tys2 => IH tys2 (*nope*)
    end)
  
  .






  ty_rect (fun _ => ty -> bool) (fun _ => ty_node_ -> bool) (fun _ => unit) t1.






Next Obligation.
intros. subst. unfold ty_size. simpl. apply Nat.lt_succ_diag_r.
Qed.
Next Obligation.
intros. subst. rewrite ty_node_size_rewrite.
(*bad*) lia.
Qed.
Next Obligation.
intros. subst. apply Forall_inv in Hl. assumption.
Defined.
Next Obligation.
intros.
subst. apply Forall_inv_tail in Hl; assumption.
Defined.
Next Obligation.
intros.
rewrite List.Forall_forall.
(*Not great proof*)
clear; intros.
rewrite ty_node_size_rewrite.
pose proof (in_split x tys H).
destruct H0 as [l1 [l2 Htys]]; subst.
rewrite map_app; simpl.
rewrite list_sum_app. simpl. unfold ty_size at 1. lia.
Qed.
Next Obligation.
intros. subst.
simpl in Hlt. lia.
Qed.
Next Obligation.
intros. subst. unfold tysymbol_size. simpl.
destruct d; simpl; auto.
Qed.


Record tysymbol_ (A: Set) : Set := {
  ts_name : ident;
  ts_args : list tvsymbol;
  ts_def : type_def (@ty_ A)
}.
 

Search In
rewrite Forall_forall.
intros.

clear. induction tys; simpl; auto.
constructor; auto.
- 


subst.


 Search Forall. rewrite ty_node_size_rewrite.

 simpl.

 Search (?x < S ?x). 


End TyInd.

(*Now can we do proof on Acc?*)
Fixpoint ty_equal (t1 t2: ty) (ACC: Acc lt (ty_size t1)) {struct ACC} : bool :=
  match t1.(ty_node), t2.(ty_node) with
  | Tyvar v1, Tyvar v2 => true
  | Tyapp ts1 tys1, Tyapp ts2 tys2 => 
    forallb (fun x => x) (map2'' tys1 tys2
      (fun x Hinx y Hiny => ty_equal x y (Acc_inv _ _ _)))
  | _, _ => false
  end.


  do 3 f_equal.
  induction l; simpl; auto.
  rewrite IHl. reflexivity.
  f_equal. f_equal. f_equal.
  unfold ty_node_size.
    (1 + match (ts_def ts) with
          | NoDef _ => 0
          | Alias _ x => 1 + (1 + ty_node_size (x.(ty_node)))
    end) +
  
   fold_right plus 0 
      (map (fun (x: ty) => ty_node_size (x.(ty_node))) tys)
  end.

Print tysymbol_.

Definition ty_size {A: Type} (sz: A -> nat)




Definition ty_size {A: Type} (sz: A -> nat) (t: @ty_ A) : nat :=





Print tysymbol_.


Print ty_.

Print ty_node_.

Variable ()
    


(*Fail Inductive tysymbol := {
  ts_name : I.ident;
  ts_args : list tvsymbol;
  ts_def: type_def ty
}
with ty := {
  ty_node : ty_node;
  ty_tag : tag
}
with ty_node_ :=
  | Tyvar : tvsymbol -> ty_node_
  | Tyapp : tysymbol -> list ty -> ty_node_.*)


(*1 version:
*)
(*Inductive tysymbol : Set :=
  | mk_tysymbol : ident -> list tvsymbol -> type_def ty -> tysymbol 
with ty : Set :=
  | mk_ty : ty_node_ -> tag -> ty
with ty_node_ : Set :=
  | Tyvar : tvsymbol -> ty_node_
  | Tyapp : tysymbol -> list ty -> ty_node_.

Definition ts_name (t: tysymbol) : ident :=
  match t with
  | mk_tysymbol i _ _ => i
  end.

Definition ts_args (t: tysymbol) : list tvsymbol :=
  match t with
  | mk_tysymbol _ l _ => l
  end.

Definition ts_def (t: tysymbol) : type_def ty :=
  match t with
  | mk_tysymbol _ _ t => t
  end.

Definition ty_node (t: ty) : ty_node_ :=
  match t with
  | mk_ty t _ => t
  end.

Definition ty_tag (t: ty) : tag :=
  match t with
  | mk_ty _ t => t
  end.*)
  
(*ts_equal and ty_equal are reference equality in OCaml impl*)
Definition ts_equal (t1 t2: tysymbol) : bool :=
  id_equal (ts_name _ t1) (ts_name _ t2).

(*End TyImpl.*)

*)














*)