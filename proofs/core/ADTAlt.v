Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.Eqdep_dec.
(*Require Import Coq.Logic.EqdepFacts.*)
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

Lemma bool_irrelevance (b: bool) (p1 p2: b): p1 = p2.
Proof.
  apply UIP_dec, bool_dec.
Qed.

Lemma is_false {P: Type}: false -> P.
Proof.
discriminate.
Qed.

Definition proj2_bool {b1 b2: bool} (x: b1 && b2) : b2 :=
  proj2 (andb_prop _ _ x).

Lemma NoDup_map_in: forall {A B: Type} {f: A -> B} {l: list A} {x1 x2: A},
  NoDup (map f l) ->
  In x1 l -> In x2 l ->
  f x1 = f x2 ->
  x1 = x2.
Proof.
  intros A B f l x1 x2 Hn Hin1 Hin2 Hfeq.
  induction l; simpl.
  - destruct Hin1.
  - simpl in *. destruct Hin1; destruct Hin2; subst; auto;
    inversion Hn; subst;
    try solve[exfalso; apply H2; 
      (rewrite Hfeq + rewrite <- Hfeq); rewrite in_map_iff; 
      (solve[exists x2; auto] + solve[exists x1; auto])].
    apply IHl; assumption.
Qed.

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

Lemma inb_spec (x: T) (l: list T): reflect (In x l) (inb x l).
Proof.
  induction l; simpl.
  - apply ReflectF; auto.
  - apply ssr.ssrbool.orPP; auto.
    destruct (T_dec x a); subst; simpl;
    [apply ReflectT | apply ReflectF]; auto.
Qed.

Definition in_type (l: list T) : Set :=
  { x : T | inb x l }.

Definition build_in_type {x: T} {l: list T} (x_in: inb x l): in_type l :=
  exist _ x x_in.

Definition in_type_extra (l: list T) (f: T -> Set) : Set :=
  {t: in_type l & f (proj1_sig t)}.

Definition build_extra {l: list T} (x: in_type l) {f: T -> Set} (y: f (proj1_sig x)) :
  in_type_extra l f :=
  existT _ x y.

Lemma in_type_eq (l: list T) (x y: in_type l):
  x = y <-> proj1_sig x = proj1_sig y.
Proof.
  destruct x as [x inx]; destruct y as [y iny]; simpl.
  split; intros.
  - apply EqdepFacts.eq_sig_fst in H; assumption.
  - subst. assert (inx = iny) by (apply bool_irrelevance); subst; reflexivity.
Qed.

Lemma in_type_dec (l: list T) (x y: in_type l): {x = y} + {x <> y}.
Proof.
  destruct (T_dec (proj1_sig x) (proj1_sig y)).
  - left. apply in_type_eq in e; auto.
  - right. intro C; subst; contradiction.
Qed.

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
(*It must be the case that the domain of the inhabited base type is inhabited*)
Variable bases_inhab: bases base_inhab.

(*We encode a particular mutual type:*)
Variable (m: mut).

(*We now define the type A (build_base):*)
Section ADef.

(*TODO: move*)
(*TODO: when we add functions, this will become more complicated*)
(*NOTE: this does NOT handle nested types (ex: tree = node of list tree)*)

(*This is a bit of overkill for now (we only want to know if a type symbol
  is an ADT/mut occurrence), but it will be useful later*)
Definition typesym_get_adt_aux (ts: typesym) : option adt :=
  fold_right (fun a acc => if string_dec (ts_name ts) (a_name a) then Some a 
    else acc) None (m_adts m).

Lemma typesym_get_adt_aux_some {ts a}:
  typesym_get_adt_aux ts = Some a ->
  inb _ adt_eq_dec a (m_adts m) /\
  ts_name ts = a_name a.
Proof.
  unfold typesym_get_adt_aux.
  induction (m_adts m); simpl; [discriminate| ].
  destruct (string_dec (ts_name ts) (a_name a0)).
  - intros eq_a; inversion eq_a; subst. destruct (adt_eq_dec a a); auto.
  - intros Htl. apply IHl in Htl. destruct Htl as [in_al eq_name];
    rewrite in_al, orb_true_r; auto.
Qed.

Lemma typesym_get_adt_aux_none ts:
  typesym_get_adt_aux ts = None ->
  forall a, inb _ adt_eq_dec a (m_adts m) ->
  ts_name ts <> a_name a.
Proof.
  unfold typesym_get_adt_aux.
  induction (m_adts m); simpl; auto.
  destruct (string_dec (ts_name ts) (a_name a)); [discriminate|].
  intros Htl a'.
  destruct (adt_eq_dec a' a); subst; auto.
Qed.

(*More convenient in proofs - we can destruct this without
  dependent pattern matching issues*)
Definition typesym_get_adt ts : 
  {a : adt | inb _ adt_eq_dec a (m_adts m) /\ ts_name ts = a_name a } +
  {forall a, inb _ adt_eq_dec a (m_adts m) ->
  ts_name ts <> a_name a}.
Proof.
  destruct (typesym_get_adt_aux ts) eqn : Hty.
  - left. apply (exist _ a). apply typesym_get_adt_aux_some, Hty.
  - right. apply typesym_get_adt_aux_none, Hty.
Qed. (*TODO: see if need to be Defined*)

Definition is_ind_occ (ind: string) (t: ty) : bool :=
  match t with
  | ty_app ts tys =>
    match (typesym_get_adt ts) with
    | inleft a => string_dec (a_name (proj1_sig a)) ind
    | inright _ => false
    end
  | _ => false
  end.

(*Is the type an occurence of any ADT in the mutual block?*)
(*
Definition is_mut_occ (t: ty) : bool :=
  match t with
  | ty_app ts tys =>
    match (typesym_get_adt ts) with
    | inleft _ => true
    | inright _ => false
    end
  | _ => false
  end.*)

(*A (non-recursive) type is interpreted according to these functions.
  Type variables are defined by a function to be given later*)
Fixpoint ty_to_set (vars: list Set) (t: ty) : Set :=
  match t with
  | ty_base b => bases b
  | ty_var v => nth v vars empty
  | ty_app ts tys =>
    match (typesym_get_adt ts) with
    | inleft _ => unit
    | inright _ => typs ts (map (ty_to_set vars) tys)
    end
  end.

(*Iterated tuple*)
Fixpoint big_sprod (l: list Set) : Set :=
  match l with
  | nil => unit
  | x :: xs => (x * (big_sprod xs))%type
  end.

  (*maybe change [ty_to_set] to include the unit part*)

(*The type for a single constructor is an iterated product of the
  representations (ty_to_set) of each of the argument types.
  We add extra units for each recursive instance. This does not
  affect the size/arguments of the type (since there is only 1
  instance of unit), but it means that the ith element of the tuple
  corresponds to the ith element of the constructor args. This will
  make the proofs later much simpler*)

Definition build_constr_base_aux (vars: list Set) (l: list ty) : Set :=
  big_sprod (map (ty_to_set vars) l).

(*The type for a single constructor*)
Definition build_constr_base (vars: list Set) (c: constr) : Set :=
  build_constr_base_aux vars (c_args c).

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
Definition num_rec_type (a: adt) (tys: list ty)  : Set :=
  {i: nat | Nat.ltb i (length tys) && 
    is_ind_occ (a_name a) (nth i tys ty_d)}.

Definition build_rec (P: list Set) (a: adt) (cs: list constr) :
  build_base P cs -> Set :=
  fun (b: build_base P cs) =>
    (*Get the constructor b belongs to*)
    let c : constr := proj1_sig (projT1 b) in  
    num_rec_type a (c_args c).

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
  c's constructor list. ([pe] just lifts n to the type level)
  But we don't just give a list, or an n-tuple/vector, because we need
  to keep track of which index in c's arg list each instance comes from.
  This will be extremely helpful later*)
Definition make_constr (P: list Set) (a: mut_in_type) (c: constr)
  (c_in: inb _ constr_eq_dec c (a_constrs (proj1_sig a)))
  (data: build_constr_base P c)
  (recs : forall (t: mut_in_type), 
    num_rec_type (proj1_sig t) (c_args c) -> mk_adts P t) : mk_adts P a :=
  mkW mut_in_type P _ _
  a (get_constr_type P (proj1_sig a) _ c c_in data) recs.

(*Now that the core encoding is finished, we prove some theorems
  (maybe helpful to prove induction here instead of later)*)

Section Theorems.

(*Inversion: For any instance of [mk_adts], we can find the constructor
  and the arguments used to create it*)

(*MUCH easier than before AND no axioms needed*)
Definition find_constr: forall (a: mut_in_type) (P: list Set) (x: mk_adts P a),
  {c: constr & {t: inb _ constr_eq_dec c (a_constrs (proj1_sig a)) *
    build_constr_base P c * 
    forall (t: mut_in_type), 
    num_rec_type (proj1_sig t) (c_args c) -> mk_adts P t |
  x = make_constr P a c (fst (fst t)) (snd (fst t)) (snd t) }}.
Proof.
  intros a P x.
  unfold mk_adts in x.
  destruct x.
  apply (existT _ (proj1_sig (projT1 a))).
  apply (exist _ ( pair (pair (proj2_sig (projT1 a)) (projT2 a)) f)).
  destruct a; destruct x; reflexivity.
Qed.

(*Disjointness: Any 2 different constructors, no matter the
  arguments they are applied to, are never equal*)

Lemma constrs_disjoint: forall (a: mut_in_type) (P: list Set) 
  (c1 c2: constr) 
  (c1_in: inb _ constr_eq_dec c1 (a_constrs (proj1_sig a)))
  (c2_in: inb _ constr_eq_dec c2 (a_constrs (proj1_sig a)))
  (b1: build_constr_base P c1)
  (b2: build_constr_base P c2)
  (recs1: forall (t: mut_in_type), 
    num_rec_type (proj1_sig t) (c_args c1) -> mk_adts P t)
  (recs2: forall (t: mut_in_type), 
    num_rec_type (proj1_sig t) (c_args c2) -> mk_adts P t),
  c1 <> c2 ->
  make_constr P a c1 c1_in b1 recs1 <> make_constr P a c2 c2_in b2 recs2.
Proof.
  intros. intro constr_eq. inversion constr_eq. subst; contradiction.
Qed.

(*Injectivity: Constructor_rep is injective*)



(*Relies on [eq_rect_eq] for case when A does not have decidable equality*)
Lemma mkW_inj (I: Set) (eqI: forall (x y: I), {x = y} + {x <> y}) 
(P: list Set) (A: list Set -> I -> Set)
  (B: forall i, I -> A P i -> Set) (i: I) (a1 a2: A P i)
  (b1: forall j, B i j a1 -> W I P A B j) (b2: forall j, B i j a2 -> W I P A B j):
  mkW I P A B i a1 b1 = mkW I P A B i a2 b2 ->
  exists (Heq: a1 = a2),
    (forall j (x: B i j a1), b1 j x = b2 j (eq_rect _ (B i j) x _ Heq)).
Proof.
intros Heq.
inversion Heq.
apply inj_pair2_eq_dec in H1; auto.
apply inj_pair2_eq_dec in H0; auto.
subst. exists eq_refl. intros. simpl.
(*NOTE: if A has decidable equality, then we don't need [eq_rect_eq].
  But we cannot assume this in general: the base types may include
  real numbers, for instance*)
apply inj_pair2 in H1; subst; reflexivity.
Qed.

(*Relies on UIP for case when A does not have decidable equality*)
Lemma constrs_inj: forall (a: mut_in_type) (P: list Set) 
(c: constr) 
(c_in: inb _ constr_eq_dec c (a_constrs (proj1_sig a)))
(b1: build_constr_base P c)
(b2: build_constr_base P c)
(recs1: forall (t: mut_in_type), 
  num_rec_type (proj1_sig t) (c_args c) -> mk_adts P t)
(recs2: forall (t: mut_in_type), 
  num_rec_type (proj1_sig t) (c_args c) -> mk_adts P t),
make_constr P a c c_in b1 recs1 = make_constr P a c c_in b2 recs2 ->
b1 = b2 /\ (forall t x, recs1 t x = recs2 t x).
Proof.
  intros.
  unfold make_constr in H.
  apply mkW_inj in H; [| apply in_type_dec].
  destruct H as [Heq recs_eq].
  unfold get_constr_type in Heq.
  unfold build_extra in Heq.
  assert (A:=Heq).
  apply inj_pair2_eq_dec in A; subst;
  [| apply in_type_dec].
  split; auto.
  (*Again, since A does not have decidable equality, we need UIP*)
  assert (Heq = eq_refl). {
    apply UIP.
  }
  subst. apply recs_eq.
Qed.

(*Induction*)

(*An induction principle for this encoding*)
Lemma w_induction
  (P: forall (a: mut_in_type) (p: list Set), mk_adts p a -> Prop):
  (*For every ADT and every constructor, *)
  (forall (a: mut_in_type) (p: list Set) (x: mk_adts p a)
    (c: constr) (c_in:  inb _ constr_eq_dec c (a_constrs (proj1_sig a)))
    (b: build_constr_base p c)
    (recs: forall (t: mut_in_type), 
      num_rec_type (proj1_sig t) (c_args c) -> mk_adts p t)
    (x_eq: x = make_constr p a c c_in b recs),
    (*if whenever P holds on all recursive instances*)
    (forall t r, P t p (recs t r)) ->
    (*then it holds for the constructor*)
    P a p x) ->

(*P holds for all instances of m*)
(forall (a: mut_in_type) (p: list Set) (x: mk_adts p a), P a p x).
Proof.
  intros IH a p.
  induction x.
  remember (mkW mut_in_type p
  (fun (p0 : list Set) (n : mut_in_type) =>
   build_base p0 (a_constrs (proj1_sig n)))
  (fun this i0 : mut_in_type =>
   build_rec p (proj1_sig i0)
     (a_constrs (proj1_sig this))) i a f) as y.
  destruct (find_constr _ _ y) as [c [[[c_in b] rec] y_eq]].
  rewrite y_eq. simpl.
  eapply IH.
  reflexivity.
  simpl in y_eq. subst. unfold make_constr in y_eq.
  apply mkW_inj in y_eq; [| apply in_type_dec].
  destruct y_eq as [a_eq rec_eq].
  subst. simpl in *.
  intros.
  rewrite <- rec_eq. apply H.
Qed.

End Theorems.

(*Higher-Level Encoding*)

(*The previous encoding uses awkward dependent types (ex: for recs in
  the constructor). Instead we want the constructor encoding to be
  a constructor applied to arguments. To ensure well-typed argumets, 
  we use a heterogenous list*)
Require Import Hlist. (*TODO factor out Hlist*)

(*The full mapping from types to Sets, where ADT instances are interpreted
  as the corresponding [mk_adts]*)
(*NOTE: (remove) unlike before, domain of ADT is definitionally equal to
  mk_adts, not propositionally equal. This reduces need for casts*)
Definition domain (p: list Set) (t: ty) : Set :=
  match t with
  | ty_app ts tys =>
    (*If ts is in m, then map to appropriate ADT*)
    match (typesym_get_adt ts) with
    | inleft a =>
      mk_adts p (build_in_type _ adt_eq_dec (proj1 (proj2_sig a)))
    | inright _ => ty_to_set p t
    end
  | _ => ty_to_set p t
  end. 

(*Convert between a [big_sprod] and an [hlist]*)

Fixpoint big_sprod_to_hlist {A: Set} {f: A -> Set} {l: list A} (x: big_sprod (map f l))
  {struct l} : hlist f l :=
  match l as l' return big_sprod (map f l') -> hlist f l' with
  | nil => fun _ => HL_nil _
  | x :: xs => fun p => HL_cons _ x xs (fst p) (big_sprod_to_hlist (snd p))
  end x.

Fixpoint hlist_to_big_sprod {A: Set} {f: A -> Set} {l: list A} (h: hlist f l) :
  big_sprod (map f l) :=
  match l as l' return hlist f l' -> big_sprod (map f l') with
  | nil => fun _ => tt
  | x :: xs => fun h => (hlist_hd h, hlist_to_big_sprod (hlist_tl h))
  end h.

Lemma hlist_to_big_sprod_inv {A: Set} {f: A -> Set} {l: list A} (x: big_sprod (map f l)):
  hlist_to_big_sprod (big_sprod_to_hlist x) = x.
Proof.
  induction l; simpl; [| rewrite IHl]; destruct x; reflexivity.
Qed.

Lemma big_sprod_to_hlist_inv {A: Set} {f: A -> Set} {l: list A} (h: hlist f l):
  big_sprod_to_hlist (hlist_to_big_sprod h) = h.
Proof.
  induction l; simpl.
  - symmetry. apply hlist_nil.
  - rewrite IHl. symmetry. apply hlist_inv.
Qed.

(*Now convert an [hlist] on [domains] to one on [ty_to_set] (ie: remove
  recursive information)*)
Fixpoint hlist_dom_to_set {p: list Set} {l: list ty} (h: hlist (domain p) l):
  hlist (ty_to_set p) l.

  refine (match l as l' return hlist (domain p) l' -> hlist (ty_to_set p) l' with
  | nil => fun _ => HL_nil _
  | x :: xs => fun h => 
    HL_cons _ x xs (match x as t return domain p t -> ty_to_set p t with
    | ty_base b => fun y => y
    | ty_var v => fun y => y
    | ty_app ts tys => _
    end (hlist_hd h)) (hlist_dom_to_set p xs (hlist_tl h))
  end h).
(*Handle [ty_app] case with tactics*)
simpl.
case (typesym_get_adt ts).
- intros _ _. exact tt.
- intros _ y. exact y.
Defined.

Definition is_rec_ty (t: ty) : bool :=
  match t with
  | ty_app ts tys => if typesym_get_adt ts then true else false
  | _ => false
  end.

Lemma is_rec_ty_eq {t: ty} (Hrec: is_rec_ty t = false) p:
  domain p t = ty_to_set p t.
Proof.
  destruct t; simpl in *; auto.
  destruct (typesym_get_adt t); simpl in *; auto.
  discriminate.
Qed.

Ltac uip_subst e := assert (e = eq_refl) by (apply UIP); subst.

(*Now we prove that, if the ith element of l is non-recursive,
  [hlist_dom_to_set] is the same as the original list*)
(*Needs UIP*)
Lemma hlist_dom_to_set_ith_nonrec {p: list Set} {l: list ty} 
  (h: hlist (domain p) l) (i: nat) (d1: ty) (d2: ty_to_set p d1)
  (d3: domain p d1) (Hrec: is_rec_ty (nth i l d1) = false):
  i < length l ->
  hnth i (hlist_dom_to_set h) d1 d2 =
    scast (is_rec_ty_eq Hrec p) (hnth i h d1 d3).
Proof.
  generalize dependent (is_rec_ty_eq Hrec p).
  generalize dependent i.
  induction l; simpl; intros.
  - inversion H.
  - destruct i.
    + destruct a.
      * uip_subst e. reflexivity.
      * uip_subst e. reflexivity. 
      * simpl in *.
        generalize dependent (hlist_hd h).
        simpl.
        destruct (typesym_get_adt t).
        -- discriminate.
        -- intros. uip_subst e. reflexivity.
    + apply IHl; auto.
      apply Arith_prebase.lt_S_n_stt in H; auto.
Qed.

Lemma is_rec_ty_unit {t: ty} (Hrec: is_rec_ty t) p:
  unit = ty_to_set p t.
Proof.
  destruct t; simpl in *; try discriminate.
  destruct (typesym_get_adt t); simpl in *; auto.
  discriminate.
Qed.

(*And likewise, if the ith element is recursive, [hlist_dom_to_set]
  gives unit*)
Lemma hlist_dom_to_set_ith_rec {p: list Set} {l: list ty} 
  (h: hlist (domain p) l) (i: nat) (d1: ty) (d2: ty_to_set p d1)
  (Hrec: is_rec_ty (nth i l d1)):
  i < length l ->
  hnth i (hlist_dom_to_set h) d1 d2 = scast (is_rec_ty_unit Hrec p) tt.
Proof.
  generalize dependent (is_rec_ty_unit Hrec p).
  generalize dependent i.
  induction l; simpl; intros.
  - inversion H.
  - destruct i.
    + destruct a; try discriminate.
      simpl in *.
      generalize dependent (hlist_hd h).
      simpl.
      destruct (typesym_get_adt t).
      -- intros _. uip_subst e. reflexivity.
      -- discriminate.
    + apply IHl; auto.
      apply Arith_prebase.lt_S_n_stt in H; auto.
Qed.

(*The first step is the build the [build_constr_base] from the hlist.
  This is conceptually simple: we just bundle the non-recursive types
  into a tuple, adding units appropriately. But we will build it in
  several smaller steps to make later proofs easier*)
Definition args_to_constr_base_aux p (l: list ty)
  (a: hlist (domain p) l): build_constr_base_aux p l :=
  hlist_to_big_sprod (hlist_dom_to_set a).


(*First, from an hlist of the arguments, build the [build_constr_base].
  Conceptually this is very simple: just go through and build the tuple with
  each non-recursive type found*)
(*It turns out to be better to mostly write this manually; we do not run into
  dependent pattern matching issues when destructing [typesym_get_adt]*)
(*Fixpoint args_to_constr_base_aux p (l: list ty)
  (a: hlist (domain p) l):
  build_constr_base_aux p l.
refine(
  match l as l' return hlist (domain p) l' -> build_constr_base_aux p l' with
  | nil => fun _ => tt
  | thd :: ttl => fun a => 
    let l' := thd :: ttl in 
    match a in (hlist _ l1) with
    | HL_nil => tt
    | HL_cons x tl ahd atl =>
      match x as x' return (domain p x') -> build_constr_base_aux p (x' :: tl) with
      | ty_base b => fun ahd => (ahd, args_to_constr_base_aux p tl atl)
      | ty_var n => fun ahd => (ahd, args_to_constr_base_aux p tl atl)
      | ty_app ts tys => _
      end ahd
    end
  end a).
  unfold build_constr_base_aux.
  simpl in *.
  case (typesym_get_adt ts).
  - intros _ _. exact (tt, args_to_constr_base_aux p tl atl).
  - intros _ y. exact (y, args_to_constr_base_aux p tl atl).
Defined.*)

Definition args_to_constr_base (p: list Set) (c: constr)
  (a: hlist (domain p) (c_args c)): build_constr_base p c :=
  args_to_constr_base_aux p (c_args c) a.

(*And build the recursive arguments*)

Definition dom_d: forall p, domain p ty_d := fun p =>
  bases_inhab.
Definition ty_set_d: forall p, ty_to_set p ty_d := fun p =>
  bases_inhab.

(*TODO: move*)
(*We require that all ADT names are unique*)
(*TODO: change to decidable version*)
Variable adt_names_uniq: NoDup (map a_name (m_adts m)).

Lemma adt_names_eq {a1 a2: adt}:
  inb _ adt_eq_dec a1 (m_adts m) ->
  inb _ adt_eq_dec a2 (m_adts m) ->
  a_name a1 = a_name a2 ->
  a1 = a2.
Proof.
  intros a1_in a2_in name_eq.
  apply (@NoDup_map_in _ _ _ _ a1 a2) in adt_names_uniq; auto.
  - apply (ssrbool.elimT (inb_spec _ _ _ _) a1_in).
  - apply (ssrbool.elimT (inb_spec _ _ _ _) a2_in).
Qed.

(*This is conceptually simple as well: the [num_rec_type]
  gives us the index of l that has the correct type, so we just
  identify that element of a. There is a bit of work to make the
  types work out and avoid dependent pattern matching errors*)
Definition args_to_ind_base_aux (p: list Set) (l: list ty)
  (a: hlist (domain p) l):
  forall t: mut_in_type,
    num_rec_type (proj1_sig t) l -> mk_adts p t.
intros t.
intros i.
(*What we want: to use hnth and to use the [is_ind_occ] hypothesis
  in i to prove that the types work out. But if we just introduce
  [hnth i a] and destruct, we get dependent pattern matching errors.
  If we are more clever, we can avoid this, as follows:*)
refine
  ((match (nth (proj1_sig i) l ty_d) as t' return
    is_ind_occ (a_name (proj1_sig t)) t' ->
    domain p t' ->  mk_adts p t with
  | ty_base b => fun f _ => is_false f
  | ty_var v => fun f _ => is_false f
  | ty_app ts tys => _
  end) (proj2_bool (proj2_sig i)) (hnth (proj1_sig i) a ty_d (dom_d _))) ; simpl.
case (typesym_get_adt ts).
- intros s.
  (*We know that these two are the same, but they are only propositionally equal,
    so we will unfortunately need a cast.*)
  (*Avoid destruct here*)
  refine (match (string_dec (a_name (proj1_sig s)) (a_name (proj1_sig t))) as b
    return b -> _ with
    | left aname_eq => _
    | right _ => fun f => is_false f
    end).
  intros _.
  set (a_eq  :=
  adt_names_eq (proj1 (proj2_sig s)) (proj2_sig t) aname_eq : proj1_sig s = proj1_sig t).
  intros rep.
  set (t':=build_in_type adt adt_eq_dec (proj1 (proj2_sig s))).
  set (pack_eq := (proj2 (in_type_eq _ adt_eq_dec (m_adts m) t' t)) a_eq :
  (build_in_type adt adt_eq_dec (proj1 (proj2_sig s))) = t).
  exact (scast (f_equal (mk_adts p) pack_eq) rep).
  (*exact (eq_rect _ (mk_adts p) rep _ pack_eq).*)
- intros _ f. exact (is_false f).
Defined.

Definition args_to_ind_base (p: list Set) (c: constr)
  (a: hlist (domain p) (c_args c)):
  forall t: mut_in_type,
    num_rec_type (proj1_sig t) (c_args c) -> mk_adts p t :=
  args_to_ind_base_aux p (c_args c) a.

Definition constr_rep (p: list Set) (a: mut_in_type) (c: constr)
  (c_in: inb _ constr_eq_dec c (a_constrs (proj1_sig a)))
  (args: hlist (domain p) (c_args c)):
  mk_adts p a :=
  make_constr p a c c_in
  (args_to_constr_base p c args)
  (args_to_ind_base p c args).

(*Now we need the inverse functions for [args_to_constr_base] and
  [args_to_ind_base]; ie. the function that takes the nonrecursive and
  recursive args and produces the [hlist]. This is made easier because of
  the extra information we included in the types*)
Section Inverse.

(*TODO: move*)
Fixpoint gen_hlist_i {A: Type} (f: A -> Type) (l: list A) (d: A)
  (g: forall (i: nat), Nat.ltb i (length l) -> f (nth i l d)) : hlist f l :=
  match l as l' return (forall (i: nat), Nat.ltb i (length l') -> f (nth i l' d)) -> hlist f l' with
  | nil => fun _ => HL_nil _
  | x :: xs => fun g => HL_cons _ x xs (g 0 eq_refl) (gen_hlist_i f xs d 
    (fun i Hi => g (S i) Hi))
  end g.

Lemma gen_hlist_i_nth {A: Type} {f: A -> Type} {l: list A} {d: A}
  {g: forall (i: nat), Nat.ltb i (length l) -> f (nth i l d)} {i: nat} d2 
  (Hi: Nat.ltb i (length l)):
  hnth i (gen_hlist_i f l d g) d d2 = g i Hi.
Proof.
  revert g.
  generalize dependent i. induction l; simpl; intros.
  - pose proof (ssrbool.elimT (PeanoNat.Nat.ltb_spec0 i 0) Hi).
    inversion H.
  - destruct i; auto.
    + (*Booleans help us to get proof irrelevance here*)
      f_equal. apply bool_irrelevance.
    + erewrite IHl. reflexivity.
Qed. 

(*It is easier to convert to an hlist and use hnth than to find the ith
  element of a big_tuple directly*)

(*Fixpoint big_sprod_to_hlist (l: list Set) (x: big_sprod l) {struct l}: 
  hlist (fun (x: Set) => (x: Type)) l :=
  match l as l' return big_sprod l' -> hlist (fun (x: Set) => (x: Type)) l' with
  | nil => fun _ => HL_nil _
  | x :: xs => fun p => HL_cons _ x xs (fst p) (big_sprod_to_hlist xs (snd p))
  end x.*)


(*Get the ith element of a [big_sprod]*)
Definition big_sprod_ith {A: Set} {f: A -> Set} {l: list A} 
  (x: big_sprod (map f l)) (i: nat) (d1: A) (d2: f d1) : f (nth i l d1) :=
  hnth i (big_sprod_to_hlist x) d1 d2.

Lemma build_constr_base_aux_nth_eq (p: list Set) (l: list ty) (i: nat)
  (Hi: Nat.ltb i (length l))
 (d: Set) (t_d: ty):
  nth i (map (ty_to_set p) l) d =
  ty_to_set p (nth i l t_d).
Proof.
  (*TODO: move*)
  erewrite Common.map_nth_inbound.
  reflexivity.
  apply(ssrbool.elimT (PeanoNat.Nat.ltb_spec0 _ _) Hi).
Qed.

(*NOTE: this won't work: these have to be Defined (I think)*)

Lemma typesym_get_adt_ind_occ ts tys ty (Heq: ty = ty_app ts tys) a:
  typesym_get_adt ts = inleft a ->
  is_ind_occ (a_name (proj1_sig a)) ty.
Proof.
subst.
unfold is_ind_occ.
destruct (typesym_get_adt ts); try discriminate.
intros C. injection C; intros Heq; subst.
destruct (string_dec _ _); auto.
Qed.

Lemma typesym_get_adt_mut_occ {p} ts tys (*ty (Heq: ty = ty_app ts tys)*)
  (bse: ty_to_set p (ty_app ts tys)) b:
  typesym_get_adt ts = inright b ->
  typs ts (map (ty_to_set p) tys).
Proof.
simpl in bse |- *.
destruct (typesym_get_adt ts); try discriminate.
intros; exact bse.
Qed.


Lemma andb_conj {b1 b2: bool} (x: b1) (y: b2): b1 && b2.
Proof.
rewrite x, y. reflexivity.
Qed.


(*Think we need dependent type*)
Definition constr_ind_to_args_aux (p: list Set) (l: list ty)
  (b: build_constr_base_aux p l)
  (recs: forall t : mut_in_type, num_rec_type (proj1_sig t) l -> mk_adts p t):
  hlist (domain p) l 

  
  .
refine (gen_hlist_i (domain p) l ty_d _).
(*Not sure if this will work*)
refine ( fun i Hi =>

(fun (t: ty) (Heq: t = nth i l ty_d) =>
match t as t' return
  t' = nth i l ty_d ->
  ty_to_set p t' ->
  domain p t' with
  | ty_app ts tys => fun Heq bse => 
  _

| ty_base b' => fun _ bse => bse
| ty_var v => fun _ bse => bse
end Heq (scast (f_equal (ty_to_set p) (eq_sym Heq))
  (big_sprod_ith b i ty_d (dom_d p))))
 (nth i l ty_d) eq_refl).
(*Handle the ty_app case here*)
simpl in bse |- *.
revert bse.
(*Need info about [ind_occ] later*)
pose proof (typesym_get_adt_ind_occ ts tys _ (eq_sym Heq)). revert H.
(*pose proof (typesym_get_adt_mut_occ ts tys bse). revert H.*)
case (typesym_get_adt ts).
- intros s Hindocc _.
  (*Have all the info for recs (why we needed Heq)*)
  set (t':= (build_in_type adt adt_eq_dec (proj1 (proj2_sig s)))).
  set (n:= exist _ i (andb_conj Hi (Hindocc  s eq_refl)) : num_rec_type (proj1_sig t') l).
  exact (recs t' n).
- intros _ _ bse.
  exact bse.

Defined.

Ltac gen_scast :=
  match goal with
  | |- context [scast ?H ?x] => generalize dependent H
  end.

  (*If we have [scast Heq1 x] and [scast Heq2 x], write the first
    in terms of the second*)
Lemma scast_switch {A B C: Set} (x: A) (Heq1: A = B) (Heq2: A = C):
  scast Heq1 x = scast (eq_trans (eq_sym Heq2) Heq1) (scast Heq2 x).
Proof.
  subst. reflexivity.
Qed.


(*One of the main lemmas we need: if the ith element of l is non-recursive,
  the the ith element of the constructed hlist is the same as the
  ith element of the original tuple*)
Lemma constr_ind_to_args_aux_nonrec {p: list Set} {l: list ty}
(b: build_constr_base_aux p l)
(recs: forall t : mut_in_type, num_rec_type (proj1_sig t) l -> mk_adts p t)
{i: nat} (Hi: i < length l) (Hnonrec: is_rec_ty (nth i l ty_d) = false):
hnth i (constr_ind_to_args_aux p l b recs) ty_d (dom_d p) = 
(scast (eq_sym (is_rec_ty_eq Hnonrec p)) (big_sprod_ith b i ty_d (dom_d p))).
Proof.
  unfold constr_ind_to_args_aux.
  set (Hi':=ssrbool.introT (PeanoNat.Nat.ltb_spec0 _ _) Hi :
      Nat.ltb i (Datatypes.length l)).
  rewrite gen_hlist_i_nth with (Hi:=Hi').
  generalize dependent (@eq_refl ty (@nth ty i l ty_d)).
  intros e.
  (*The core problem is that we cannot destruct [nth i l ty_d]
    because it is needed in the proof to build the [num_rec_type].
    We have to generalize our goal to match on any t which is equal
    to [nth i l ty_d]. The goal is large, so we do this in the following
    match:*)
  match goal with
  | |- match nth i l ty_d as t' in ty return (t' = nth i l ty_d -> ty_to_set p t' -> domain p t')
      with
      | ty_base b' => ?aa
      | ty_var v => ?bb
      | ty_app ts tys => ?cc
      end ?f ?g = ?y =>
    assert (forall (t: ty) (Heq: t = nth i l ty_d),
      match t as t' return (t' = nth i l ty_d -> ty_to_set p t' -> domain p t')
      with
      | ty_base b' => aa
      | ty_var v => bb
      | ty_app ts tys => cc
      end Heq 
      (scast (f_equal (ty_to_set p) (eq_sym Heq)) (big_sprod_ith b i ty_d (dom_d p)))
      = 
      scast 
     (eq_trans  (eq_sym (is_rec_ty_eq Hnonrec p))
        (eq_sym (f_equal (domain p) Heq)))
      (big_sprod_ith b i ty_d (dom_d p))
    
    )
  end.
  {
    intros t.
    destruct t; intros Heq.
    - apply scast_eq_uip.
    - apply scast_eq_uip. 
    - (*Get both [scasts] in terms of a single value, so we can
        generalize (needed to destruct [typesym_get_adt t])*) 
      match goal with
      |- _ = scast ?H ?x =>
        rewrite scast_switch with (Heq2:=H);
        generalize dependent (scast H x)
      end. intros d.
      gen_scast.
      revert d.
      generalize dependent (typesym_get_adt_ind_occ t l0 (nth i l ty_d) (eq_sym Heq)).
      (*Need all this so we can destruct [typesym_get_adt t]*)
      rewrite <- Heq in Hnonrec. revert Hnonrec. simpl.
      destruct (typesym_get_adt t); try discriminate.
      intros.
      uip_subst e0. reflexivity.
  }
  specialize (H (nth i l ty_d) e).
  simpl in H |- *.
  rewrite H.
  apply scast_eq_uip.
Qed.

Lemma big_sprod_ext {A: Set} {f: A -> Set} (l: list A) 
  (x1 x2: big_sprod (map f l)) (d1: A) (d2: f d1)
  (Hext: forall i, i < length l -> big_sprod_ith x1 i d1 d2 = big_sprod_ith x2 i d1 d2):
  x1 = x2.
Proof.
  (*Use inverse functions*)
  rewrite <- (hlist_to_big_sprod_inv x1), <- (hlist_to_big_sprod_inv x2).
  f_equal.
  apply hlist_ext_eq with (d:=d1)(d':=d2).
  apply Hext.
Qed.

Lemma ty_to_set_rec p {t: ty}:
  is_rec_ty t ->
  ty_to_set p t = unit.
Proof.
  destruct t; simpl; try discriminate.
  destruct (typesym_get_adt); auto; discriminate.
Qed.

(*Now, the proofs of the inverse:*)
Lemma constr_ind_args_inv_aux1 {p: list Set} {l: list ty}
(b: build_constr_base_aux p l)
(recs: forall t : mut_in_type, num_rec_type (proj1_sig t) l -> mk_adts p t):
args_to_constr_base_aux p l (constr_ind_to_args_aux p l b recs) = b.
Proof.
  (*We want to prove that the ith elements are equal*)
  eapply big_sprod_ext with (d1:=ty_d)(d2:=ty_set_d p).
  intros i Hi.
  unfold args_to_constr_base_aux, big_sprod_ith.
  rewrite big_sprod_to_hlist_inv.
  destruct (is_rec_ty (nth i l ty_d)) eqn : Hrec.
  - (*If recursive, unit*) 
    rewrite (hlist_dom_to_set_ith_rec _ i _ _ Hrec Hi).
    generalize dependent (is_rec_ty_unit Hrec p). 
    generalize dependent (hnth i (big_sprod_to_hlist b) ty_d (ty_set_d p)).
    rewrite (ty_to_set_rec p Hrec).
    intros. uip_subst e. destruct t. reflexivity.
  - (*If non-recursive, use previous result*)
    rewrite (hlist_dom_to_set_ith_nonrec _ i _ _ (dom_d p) Hrec Hi).
    rewrite constr_ind_to_args_aux_nonrec with (Hnonrec:=Hrec); auto.
    rewrite scast_scast.
    generalize dependent (eq_trans (eq_sym (is_rec_ty_eq Hrec p))
    (is_rec_ty_eq Hrec p)).
    intros e. uip_subst e.
    reflexivity.
Qed.

End Inverse.

End Encode.

End ADT.
