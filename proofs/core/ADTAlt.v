Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

From mathcomp Require all_ssreflect. (*fintype finfun.*)

Set Bullet Behavior "Strict Subproofs".

Coercion proj_sumbool (A B: Prop) (H: {A} + {B}) : bool :=
  if H then true else false.
Coercion is_true : bool >-> Sortclass.

(*TODO: Separate file*)
Section Util.

Inductive ForallT {A: Type} (P: A -> Type) : list A -> Type :=
  | ForallT_nil: ForallT P nil
  | ForallT_cons: forall {x: A} {l: list A},
    P x -> ForallT P l -> ForallT P (x :: l).

Lemma ForallT_hd {A: Type} {P: A -> Type} {x: A} {l: list A}:
  ForallT P (x :: l) ->
  P x.
Proof.
  intros. inversion X; subst. apply X0.
Qed.

Lemma ForallT_tl {A: Type} {P: A -> Type} {x: A} {l: list A}:
  ForallT P (x :: l) ->
  ForallT P l.
Proof.
  intros. inversion X; auto.
Qed.

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

End Util.

(*TODO: move*)
(*In many places, we need the type {x : T | in x l} and the type T is
  decidable. We give utilities here for this type*)
Module InType.

(*First do without ssreflect, do we need?*)
Section InTypeDef.
Variable (T: Set). (*Set?*)
Variable (T_dec: forall (x y: T), {x = y} + {x <> y}).

Definition inb (x: T) (l: list T) : bool :=
  fold_right (fun y acc => ((T_dec x y) || acc)) false l.

Definition in_type (l: list T) : Set :=
  { x : T | inb x l }.

Definition build_in_type {x: T} {l: list T} (x_in: inb x l): in_type l :=
  exist _ x x_in.

Definition in_type_extra (l: list T) (f: T -> Set) : Set :=
  {t: in_type l & f (proj1_sig t)}.

Definition build_extra {l: list T} (x: in_type l) {f: T -> Set} (y: f (proj1_sig x)) :
  in_type_extra l f :=
  existT _ x y.

(*TODO: prove finite and stuff? If so, need ssreflect*)
End InTypeDef.

End InType.

Import InType.

Section ADT.

(*The base types (with decidable equality - we may be able to remove
  this restriction but likely not, and it would make things MUCH worse)*)
Variable base: Set.
Variable base_inhab: base.
Variable base_dec: forall (x y: base), {x = y} + {x <> y}.


(*TODO: use ssreflect? and eqType*)

(*Type variables are represented by nats, representing their position in
  the list of arguments: ex, for (either A B), we have Left, which takes
  argument (ty_var 0) and Right, which takes (ty_var 1)*)

(*Type symbol names are represented by strings*)
(*For now (until maybe we add dependent types), just take in number of
  polymoprhic arguments *)
Record typesym : Set := {ts_name: string; ts_args: nat}.

Unset Elimination Schemes.
Inductive ty : Set :=
  | ty_base: base -> ty
  | ty_var: nat -> ty (*Problem: nat can be too large maybe? defaults or what?*)
  | ty_app: typesym -> list ty -> ty
  (*TODO: add functions*).
Set Elimination Schemes.

(*Induction principles for [ty]*)
Section TyInd.

Variable (P: ty -> Prop).
Variable (Pbase: forall (b: base), P (ty_base b)).
Variable (Pvar: forall (n: nat), P (ty_var n)).
Variable (Papp: forall (ts: typesym) (tys: list ty),
  Forall P tys -> P (ty_app ts tys)).

Fixpoint ty_ind (t: ty) : P t :=
  match t with
  | ty_base b => Pbase b
  | ty_var n => Pvar n
  | ty_app ts tys =>
    Papp ts tys
    ((fix ty_nest (l: list ty) : Forall P l :=
      match l with
      | nil => Forall_nil _
      | x :: xs => Forall_cons _ (ty_ind x) (ty_nest xs)
      end) tys)
  end.

End TyInd.


(*TODO: There has to be a better way*)
Section TyRect.

Variable (P: ty -> Type).
Variable (Pbase: forall (b: base), P (ty_base b)).
Variable (Pvar: forall (n: nat), P (ty_var n)).
Variable (Papp: forall (ts: typesym) (tys: list ty),
  ForallT P tys -> P (ty_app ts tys)).

Fixpoint ty_rect (t: ty) : P t :=
  match t with
  | ty_base b => Pbase b
  | ty_var n => Pvar n
  | ty_app ts tys =>
    Papp ts tys
    ((fix ty_nest (l: list ty) : ForallT P l :=
      match l with
      | nil => ForallT_nil _
      | x :: xs => ForallT_cons _ (ty_rect x) (ty_nest xs)
      end) tys)
  end.

End TyRect.

(*Constructors have names and a list of types*)
Record constr : Set := {c_name: string; c_args: list ty}.

(*ADTs have names, a number of type paramters, and a list of constructors*)
Record adt : Set := {a_name: string; a_params: nat; a_constrs: list constr}.

(*Mutual blocks consist of a list of ADTs*)
Record mut : Set := {m_adts: list adt}.

(*TODO: is there ssreflect to do this?
  "apply" at bottom: ex: if we have P1 -> P1 -> Q and lemma P -> Q,
    transforms to P1 -> P2 -> P*)

(*Decidable Equality*)
Section Eq.
Import all_ssreflect. 

(*TODO: move both of these to some "Util"*)

(*A version of "reflect_dec" with better computational behavior:
  it reduces even if the "reflect" predicate is opaque*)
Definition reflect_dec' {P} {b} (H: reflect P b): {P} + {~P} :=
  match b as b1 return b = b1 -> _ with
  | true => fun Heq => left (elimT H Heq)
  | false => fun Hneq => right (elimF H Hneq)
  end erefl.

Definition typesym_eqb (t1 t2: typesym) : bool :=
  String.eqb (ts_name t1) (ts_name t2) &&
  Nat.eqb (ts_args t1) (ts_args t2).

Ltac reflF :=
  let C := fresh in
  intros; apply ReflectF; intro C; inversion C; subst; contradiction.
  
Lemma typesym_eqb_spec (t1 t2: typesym) : reflect (t1 = t2) (typesym_eqb t1 t2).
Proof.
  rewrite /typesym_eqb.
  case: (String.eqb_spec _ _); last by reflF.
  case: (PeanoNat.Nat.eqb_spec _ _); last by reflF. 
  (*TODO: ssreflect should be able to do this I am sure*)
  move=> args_eq names_eq; apply ReflectT; move: args_eq names_eq.
  by case: t1; case: t2 => n1 a1 n2 a2/=->->.
Qed.

Definition typesym_eq_dec (t1 t2: typesym) : {t1 = t2} + {t1 <> t2} :=
  reflect_dec' (typesym_eqb_spec t1 t2).

Fixpoint ty_eqb (t1 t2: ty) {struct t1} : bool :=
  match t1, t2 with
  | ty_base b1, ty_base b2 => base_dec b1 b2
  | ty_var n1, ty_var n2 => Nat.eqb n1 n2
  | ty_app ts1 tys1, ty_app ts2 tys2 =>
    typesym_eqb ts1 ts2 &&
    (Nat.eqb (length tys1) (length tys2)) && 
    all id (map2 ty_eqb tys1 tys2)
  | _, _ => false
  end.

Lemma ty_eqb_eq: forall t1 t2,
  ty_eqb t1 t2 -> t1 = t2.
Proof.
  move=> t1; elim: t1 =>/=[ b1 t2 | n1 t2 | ts1 tys1 Hall t2];
  case: t2 =>[b2 | n2 | ts2 tys2]//.
  - by case: (base_dec b1 b2)=>//=->.
  - by move=>/PeanoNat.Nat.eqb_spec ->.
  - case: (typesym_eqb_spec _ _)=>//= ->.
    case: (PeanoNat.Nat.eqb_spec _ _)=>//=.
    move=> len_eq all_eq. f_equal.
    move: Hall tys2 len_eq all_eq .
    elim: tys1 =>[_ [|//] // | x tl IH Hall [//|x2 tl2] /= [] len_eq 
      /andP[Hh Ht] ].
    by rewrite (Forall_inv Hall _ Hh) (IH (Forall_inv_tail Hall) _ len_eq Ht).
Qed.

Lemma ty_eq_eqb: forall t1 t2,
  t1 = t2 ->
  ty_eqb t1 t2.
Proof.
  elim =>/=[b t2 <-| n t2 <- |ts tys Hall t2 <-].
  - by case: (base_dec b b).
  - by apply /PeanoNat.Nat.eqb_spec.
  - case: (typesym_eqb_spec) =>//= _.
    case: (PeanoNat.Nat.eqb_spec)=>//=_.
    move: Hall. elim: tys => [//|x tl IH Hall/=].
    rewrite (Forall_inv Hall) //=.
    by apply (IH (Forall_inv_tail Hall)).
Qed.

Lemma ty_eqb_spec (t1 t2: ty):
  reflect (t1 = t2) (ty_eqb t1 t2).
Proof.
  by apply iff_reflect; split; [apply ty_eq_eqb | apply ty_eqb_eq].
Qed.

Definition ty_eq_dec (t1 t2: ty): {t1 = t2} + {t1 <> t2} :=
  reflect_dec' (ty_eqb_spec t1 t2).

(*Equality on lists*)
Fixpoint list_eqb {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
(l1 l2: list A) : bool :=
  match l1, l2 with
  | x1 :: t1, x2 :: t2 => eq_dec x1 x2 && list_eqb eq_dec t1 t2
  | nil, nil => true
  | _, _ => false
  end.

Lemma list_eqb_spec {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
(l1 l2: list A) : reflect (l1 = l2) (list_eqb eq_dec l1 l2).
Proof.
  move: l2. elim: l1 => [[/=|/=]|x1 t1 IH [/=|x2 t2/=]]; try by reflF.
  - by apply ReflectT.
  - case: (eq_dec x1 x2)=>//=[->|]; last by reflF.
    by case: (IH t2)=>[->|]; [apply ReflectT | reflF].
Qed.

Definition list_eq_dec {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
(l1 l2: list A) : {l1 = l2} + {l1 <> l2} := reflect_dec' (list_eqb_spec eq_dec l1 l2).

(*The others are much easier*)
Definition constr_eqb (c1 c2: constr) : bool :=
  String.eqb (c_name c1) (c_name c2) &&
  list_eqb ty_eq_dec (c_args c1) (c_args c2).

Lemma constr_eqb_spec (c1 c2: constr) : reflect (c1 = c2) (constr_eqb c1 c2).
Proof.
  case: c1; case: c2 => n1 a1 n2 a2; rewrite /constr_eqb/=.
  case: String.eqb_spec=>//=[->|]; last by reflF.
  case: list_eqb_spec=>[->|]; last by reflF.
  by apply ReflectT.
Qed.

Definition constr_eq_dec (c1 c2: constr): {c1 = c2} + {c1 <> c2} :=
  reflect_dec' (constr_eqb_spec c1 c2).

Definition adt_eqb (a1 a2: adt) : bool :=
  String.eqb (a_name a1) (a_name a2) &&
  Nat.eqb (a_params a1) (a_params a2) &&
  list_eqb constr_eq_dec (a_constrs a1) (a_constrs a2).

Lemma adt_eqb_spec (a1 a2: adt) : reflect (a1 = a2) (adt_eqb a1 a2).
Proof.
  case: a1; case: a2 => n1 p1 c1 n2 p2 c2; rewrite /adt_eqb/=.
  case: String.eqb_spec=>//=[->|]; last by reflF.
  case: PeanoNat.Nat.eqb_spec=>//=[->|]; last by reflF.
  case: list_eqb_spec=>[->|]; last by reflF.
  by apply ReflectT.
Qed.

Definition adt_eq_dec (a1 a2: adt): {a1 = a2} + {a1 <> a2} :=
  reflect_dec' (adt_eqb_spec a1 a2).

Definition mut_eqb (m1 m2: mut) : bool :=
  list_eqb adt_eq_dec (m_adts m1) (m_adts m2).

Lemma mut_eqb_spec (m1 m2: mut) : reflect (m1 = m2) (mut_eqb m1 m2).
Proof.
  rewrite /mut_eqb. case: m1; case: m2 => a1 a2/=.
  case: list_eqb_spec=>[->|]; last by reflF.
  by apply ReflectT.
Qed.

Definition mut_eq_dec (m1 m2: mut): {m1 = m2} + {m1 <> m2} :=
  reflect_dec' (mut_eqb_spec m1 m2).

End Eq.


(*Basic definitions for W-types*)

Section W.
(*I is the index in the mutual block.
  P gives the information for (uniform) polymorphism
  A is the non-recursive data for each constructor
  B tells the number of recursive arguments for each constructor*)
(*Note: to add non-uniformity, P is no longer a parameter, instead
  B will take in a (list Set) as well, W will have type I -> (list Set) -> Set,
  and f will take in such a list *)
Variable (I: Set).
Variable (P: list Set).
Variable (A: (list Set) -> I -> Set).
Variable (B: forall (i: I) (j: I), A P i -> Set).
(*TODO: see about argument order*)

Inductive W : I -> Set :=
  | mkW : forall (i: I) (a: A P i) (f: forall j, B i j a -> W j), W i.

End W.

(*TODO: move*)
Inductive empty := .

Section Encode.

(*All encodings for previously-declared (or abstract) type symbols
  are given by a function typs.
  This is allows to return anything when the length of the list is wrong*)
(*TODO: Type?*)
Variable (typs: typesym -> list Set -> Set).
(*The user also specifies how base types (e.g. unit, bool, etc) are
  interpreted*)
Variable (bases: base -> Set).

(*We encode a particular mutual type:*)
Variable (m: mut).

(*A (non-recursive) type is interpreted according to these functions.
  Type variables are defined by a function to be given later*)
Fixpoint ty_to_set (vars: list Set) (t: ty) : Set :=
  match t with
  | ty_base b => bases b
  | ty_var v => nth v vars empty
  | ty_app ts tys => typs ts (map (ty_to_set vars) tys)
  end.

(*We now define the type A (build_base):*)
Section ADef.

(*TODO: move*)
(*TODO: when we add functions, this will become more complicated*)
(*NOTE: this does NOT handle nested types (ex: tree = node of list tree)*)
Definition is_ind_occ (ind: string) (t: ty) : bool :=
  match t with
  | ty_app ts tys => string_dec ind (ts_name ts)
  | _ => false
  end.

(*Get all declared ADT names in a mutual block*)
Definition mut_names (m: mut) : list string :=
  map a_name (m_adts m).

(*Filter out the recursive instances*)
Definition get_nonind_vtys (l: list ty) : list ty :=
  filter (fun v =>
    forallb (fun ind => is_ind_occ ind v) (mut_names m)) l.

(*Iterated tuple*)
Fixpoint big_sprod (l: list Set) : Set :=
  match l with
  | nil => unit
  | [x] => x
  | x :: xs => (x * (big_sprod xs))%type
  end.

(*The type for a single constructor*)
Definition build_constr_base (vars: list Set) (c: constr) : Set :=
  big_sprod (map (ty_to_set vars) (get_nonind_vtys (c_args c))).

Definition build_base (vars: list Set) (cs: list constr) : Set :=
  in_type_extra _ constr_eq_dec cs (build_constr_base vars).

End ADef.

(*Now construct B*)
Section B.

(*There are several ways we could encode B. But the easiest one will be
  to use as our type {i | i < length (c_args) && 
    ts_name (nth i (c_args)) = a}, where a 
  is the ADT we are interested in. This type has as many elements are there are
  recursive instances. But knowing each index in the arg list that each recursive
  instance corresponds to will be helpful later.
  *)

(*A default constructor*)
Definition c_d: constr := Build_constr "" nil. 
Definition ty_d : ty := ty_base base_inhab.

(*The type in question: how many recursive instances of adt a appear in
  a list tys*)
Definition num_rec_ty (P: list Set) (a: adt) (tys: list ty)  : Set :=
  {i: nat | Nat.ltb i (length tys) && 
    is_ind_occ (a_name a) (nth i tys ty_d)}.

Definition build_rec (P: list Set) (a: adt) (cs: list constr) :
  build_base P cs -> Set :=
  fun (b: build_base P cs) =>
    (*Get the constructor b belongs to*)
    let c : constr := proj1_sig (projT1 b) in  
    num_rec_ty P a (c_args c).

(*Get the index of the *)
(*
Definition build_rec_idx {P: list Set} {a: adt} {cs: list constr}
  {b: build_base P cs} (r: build_rec P a cs b) : nat :=
  proj1_sig r.
*)
End B.

(*I and P are easy: I is just a type with |m| elements
  (we use {a | a in m}), and P *)

(*Our encoding*)
Definition mut_in_type : Set := in_type adt adt_eq_dec (m_adts m).

(*This handles mutual recursion (but not nested recursion at the moment).
  Mutual recursion is not too bad, we just need to be careful to call [build_rec]
  with the correct typesym to count.*)
Definition mk_adts (P: list Set) : mut_in_type -> Set :=
  W mut_in_type P (fun p n => build_base p (a_constrs (proj1_sig n)))
  (fun this i => build_rec P (proj1_sig i) (a_constrs (proj1_sig this))).


(*Constructors*)

(*From a given constructor and the non-recursive data, build the type A*)
Definition get_constr_type (P: list Set) (a: adt) (cs: list constr) (c: constr)
  (c_in: inb _ constr_eq_dec c cs)
  (data: build_constr_base P c):
  build_base P cs :=
  build_extra _ constr_eq_dec (build_in_type _ constr_eq_dec c_in) data.

(*Note the weird type of [recs]. This says that we have n instances of 
  [mk_adts P t], where n is the number of times t occurs recursively in
  c's constructor list. ([num_rec_ty] just lifts n to the type level)
  But we don't just give a list, or an n-tuple/vector, because we need
  to keep track of which index in c's arg list each instance comes from.
  This will be extremely helpful later*)
Definition make_constr (P: list Set) (a: mut_in_type) (c: constr)
  (c_in: inb _ constr_eq_dec c (a_constrs (proj1_sig a)))
  (data: build_constr_base P c)
  (recs : forall (t: mut_in_type), 
    num_rec_ty P (proj1_sig t) (c_args c) -> mk_adts P t) : mk_adts P a :=
  mkW mut_in_type P _ _
  a (get_constr_type P (proj1_sig a) _ c c_in data) recs.

End Encode.

End ADT.
