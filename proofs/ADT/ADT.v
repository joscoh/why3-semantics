Require Export Coq.Strings.String.

(*Require Import Coq.Logic.EqdepFacts.*)
(*Import ListNotations.*)
Require Export Hlist.
Require Export ADTUtil.
Require Export Coq.Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

Section ADT.

(*Type variables - we use a nominal encoding*)
Variable typevar: Set.
Variable typevar_dec: forall (x y: typevar), {x = y} + {x <> y}.

(*The base types (with decidable equality - we may be able to remove
  this restriction but likely not, and it would make things MUCH worse)*)
Variable base: Set.
Variable base_inhab: base.
Variable base_dec: forall (x y: base), {x = y} + {x <> y}.
(*The user also specifies how base types (e.g. unit, bool, etc) are
  interpreted*)
Variable (bases: base -> Set).
(*It must be the case that the domain of the inhabited base type is inhabited*)
Variable bases_inhab: bases base_inhab.

(*Type variables are represented by nats, representing their position in
  the list of arguments: ex, for (either A B), we have Left, which takes
  argument (ty_var 0) and Right, which takes (ty_var 1)*)

(*Type symbol names are represented by strings*)
(*For now (until maybe we add dependent types), just take in number of
  polymoprhic arguments *)
Record typesym : Set := {ts_name: string; ts_args: list typevar}.

Unset Elimination Schemes.
Inductive ty : Set :=
  | ty_base: base -> ty
  | ty_var: typevar -> ty
  | ty_app: typesym -> list ty -> ty
  (*TODO: add functions*).
Set Elimination Schemes.

(*Induction principles for [ty]*)
Section TyInd.

Variable (P: ty -> Prop).
Variable (Pbase: forall (b: base), P (ty_base b)).
Variable (Pvar: forall (v: typevar), P (ty_var v)).
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
Variable (Pvar: forall (v: typevar), P (ty_var v)).
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

(*We will allow additional metadata for all of the datatypes,
  provided that this metadata has decidable equality.
  It is not used in the encoding but makes things more
  convenient for users.*)
Variable constr_data: Set.
Variable constr_data_dec: forall (x y: constr_data), {x = y} + {x <> y}.

(*Constructors have names and a list of types*)
Record constr : Set := {c_name: string; c_args: list ty; c_data: constr_data}.

Variable adt_data: Set.
Variable adt_data_dec: forall (x y: adt_data), {x = y} + {x <> y}.

(*ADTs have names, a number of type paramters, and a list of constructors*)
Record adt : Set := {a_name: string; a_params: list typevar; a_constrs: list constr;
  a_data: adt_data}.

Variable mut_data: Set.
Variable mut_data_dec: forall (x y: mut_data), {x = y} + {x <> y}.

(*Mutual blocks consist of a list of ADTs*)
Record mut : Set := {m_adts: list adt; m_data: mut_data}.

(*Decidable Equality*)
Section Eq.
Import all_ssreflect. 

Definition typesym_eqb (t1 t2: typesym) : bool :=
  String.eqb (ts_name t1) (ts_name t2) &&
  list_eqb typevar_dec (ts_args t1) (ts_args t2).
  
Lemma typesym_eqb_spec (t1 t2: typesym) : reflect (t1 = t2) (typesym_eqb t1 t2).
Proof.
  case: t1; case: t2 => n1 a1 n2 a2.
  rewrite /typesym_eqb/=.
  case: (String.eqb_spec _ _)=>[->|]; last by reflF.
  case: list_eqb_spec=> [->|]; last by reflF.
  by apply ReflectT.
Qed.

Definition typesym_eq_dec (t1 t2: typesym) : {t1 = t2} + {t1 <> t2} :=
  reflect_dec' (typesym_eqb_spec t1 t2).

Fixpoint ty_eqb (t1 t2: ty) {struct t1} : bool :=
  match t1, t2 with
  | ty_base b1, ty_base b2 => base_dec b1 b2
  | ty_var v1, ty_var v2 => typevar_dec v1 v2
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
  - by case: typevar_dec=>//=->.
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
  - by case: typevar_dec.
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

Definition constr_eqb (c1 c2: constr) : bool :=
  String.eqb (c_name c1) (c_name c2) &&
  list_eqb ty_eq_dec (c_args c1) (c_args c2) &&
  constr_data_dec (c_data c1) (c_data c2).

Lemma constr_eqb_spec (c1 c2: constr) : reflect (c1 = c2) (constr_eqb c1 c2).
Proof.
  case: c1; case: c2 => n1 a1 d1 n2 a2 d2; rewrite /constr_eqb/=.
  case: String.eqb_spec=>//=[->|]; last by reflF.
  case: list_eqb_spec=>[->|]; last by reflF.
  case: constr_data_dec =>/=[->| Hneq]; last by reflF.
  by apply ReflectT.
Qed.

Definition constr_eq_dec (c1 c2: constr): {c1 = c2} + {c1 <> c2} :=
  reflect_dec' (constr_eqb_spec c1 c2).

Definition adt_eqb (a1 a2: adt) : bool :=
  String.eqb (a_name a1) (a_name a2) &&
  list_eqb typevar_dec (a_params a1) (a_params a2) &&
  list_eqb constr_eq_dec (a_constrs a1) (a_constrs a2) &&
  adt_data_dec (a_data a1) (a_data a2).

Lemma adt_eqb_spec (a1 a2: adt) : reflect (a1 = a2) (adt_eqb a1 a2).
Proof.
  case: a1; case: a2 => n1 p1 c1 d1 n2 p2 c2 d2; rewrite /adt_eqb/=.
  case: String.eqb_spec=>//=[->|]; last by reflF.
  case: list_eqb_spec=>[->|]; last by reflF.
  case: list_eqb_spec=>[->|]; last by reflF.
  case: adt_data_dec =>/=[->|]; last by reflF.
  by apply ReflectT.
Qed.

Definition adt_eq_dec (a1 a2: adt): {a1 = a2} + {a1 <> a2} :=
  reflect_dec' (adt_eqb_spec a1 a2).

Definition mut_eqb (m1 m2: mut) : bool :=
  list_eqb adt_eq_dec (m_adts m1) (m_adts m2) &&
  mut_data_dec (m_data m1) (m_data m2).

Lemma mut_eqb_spec (m1 m2: mut) : reflect (m1 = m2) (mut_eqb m1 m2).
Proof.
  rewrite /mut_eqb. case: m1; case: m2 => a1 d1 a2 d2/=.
  case: list_eqb_spec=>[->|]; last by reflF.
  case: mut_data_dec=>/=[->|]; last by reflF.
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
Definition poly_map : Type := typevar -> Set.
Variable (I: Set).
Variable (P: poly_map).
Variable (A: poly_map -> I -> Set).
Variable (B: forall (i: I) (j: I), A P i -> Set).
(*TODO: see about argument order*)

Inductive W : I -> Set :=
  | mkW : forall (i: I) (a: A P i) (f: forall j, B i j a -> W j), W i.

End W.

Section Encode.

(*All encodings for previously-declared (or abstract) type symbols
  are given by a function typs.
  This is allows to return anything when the length of the list is wrong*)
Variable (typs: typesym -> list ty -> Set).

(*We encode a particular mutual type:*)
Variable (m: mut).

(*Before defining the encoding, we first need an operation to
  get the ADT from a given type*)
Section GetADT.

(*TODO: when we add functions, this will become more complicated*)
(*NOTE: this does NOT handle nested types (ex: tree = node of list tree)*)
Definition typesym_get_adt_aux (ts: typesym) : option adt :=
  fold_right (fun a acc => if string_dec (ts_name ts) (a_name a) then Some a 
    else acc) None (m_adts m).

    (*Avoid "auto" here; we need to make sure everything reduces*)
Lemma typesym_get_adt_aux_some {ts a}:
  typesym_get_adt_aux ts = Some a ->
  inb adt_eq_dec a (m_adts m) /\
  ts_name ts = a_name a.
Proof.
  unfold typesym_get_adt_aux.
  induction (m_adts m); simpl; [discriminate| ].
  destruct (string_dec (ts_name ts) (a_name a0)).
  - intros eq_a; injection eq_a; intros; subst. 
    destruct (adt_eq_dec a a); simpl; try assumption.
    + split; [reflexivity | assumption].
    + split; try assumption. contradiction. 
  - intros Htl. apply IHl in Htl. destruct Htl as [in_al eq_name];
    rewrite in_al, orb_true_r. split;[reflexivity | exact eq_name].
Defined.

Lemma typesym_get_adt_aux_none ts:
  typesym_get_adt_aux ts = None ->
  forall a, inb adt_eq_dec a (m_adts m) ->
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
  {a : adt | inb adt_eq_dec a (m_adts m) /\ ts_name ts = a_name a } +
  {forall a, inb adt_eq_dec a (m_adts m) ->
  ts_name ts <> a_name a}.
Proof.
  destruct (typesym_get_adt_aux ts) eqn : Hty.
  - left. apply (exist _ a). apply typesym_get_adt_aux_some, Hty.
  - right. apply typesym_get_adt_aux_none, Hty.
Defined.

Definition is_ind_occ (ind: string) (t: ty) : bool :=
  match t with
  | ty_app ts tys =>
    match (typesym_get_adt ts) with
    | inleft a => string_dec (a_name (proj1_sig a)) ind
    | inright _ => false
    end
  | _ => false
  end.

Definition is_rec_ts (ts: typesym) : bool :=
  if typesym_get_adt ts then true else false.

Definition is_rec_ty (t: ty) : bool :=
  match t with
  | ty_app ts _ => is_rec_ts ts
  | _ => false
  end.

Lemma ind_occ_is_rec_ty {a} {t: ty}:
  is_ind_occ a t ->
  is_rec_ty t.
Proof.
  unfold is_ind_occ, is_rec_ty, is_rec_ts.
  destruct t; auto.
  destruct (typesym_get_adt t); auto.
Qed.

End GetADT.

(*We now define the type A (build_base):*)
Section ADef.

(*A (non-recursive) type is interpreted according to these functions.
  Type variables are defined by a function to be given later*)
Definition ty_to_set (vars: poly_map) (t: ty) : Set :=
  match t with
  | ty_base b => bases b
  | ty_var v => vars v (*nth v vars empty*)
  | ty_app ts tys =>
    match (typesym_get_adt ts) with
    | inleft _ => unit
    | inright _ => typs ts tys (*(map (ty_to_set vars) tys)*)
    end
  end.

(*The type for a single constructor is an iterated product of the
  representations (ty_to_set) of each of the argument types.
  We add extra units for each recursive instance. This does not
  affect the size/arguments of the type (since there is only 1
  instance of unit), but it means that the ith element of the tuple
  corresponds to the ith element of the constructor args. This will
  make the proofs later much simpler*)

Definition build_constr_base_aux (vars: poly_map) (l: list ty) : Set :=
  big_sprod (map (ty_to_set vars) l).

(*The type for a single constructor*)
Definition build_constr_base (vars: poly_map) (c: constr) : Set :=
  build_constr_base_aux vars (c_args c).

Definition build_base (vars: poly_map) (cs: list constr) : Set :=
  in_type_extra constr_eq_dec cs (build_constr_base vars).

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
Definition ty_d : ty := ty_base base_inhab.

(*The type in question: how many recursive instances of adt a appear in
  a list tys*)
Definition num_rec_type (a: adt) (tys: list ty)  : Set :=
  {i: nat | Nat.ltb i (length tys) && 
    is_ind_occ (a_name a) (nth i tys ty_d)}.

(*Could generalize to bool pred like ssr?*)
Lemma num_rec_type_eq {a: adt} {tys: list ty}
  (x1 x2: num_rec_type a tys):
  proj1_sig x1 = proj1_sig x2 ->
  x1 = x2.
Proof.
  intros. destruct x1; destruct x2; simpl in *.
  subst. f_equal. apply bool_irrelevance.
Qed.

Definition build_rec (P: poly_map) (a: adt) (cs: list constr) :
  build_base P cs -> Set :=
  fun (b: build_base P cs) =>
    (*Get the constructor b belongs to*)
    let c : constr := proj1_sig (projT1 b) in  
    num_rec_type a (c_args c).

End B.

(*I and P are easy: I is just a type with |m| elements
  (we use {a | a in m}), and P *)

(*Our encoding*)
Definition mut_in_type : Set := in_type adt_eq_dec (m_adts m).

(*This handles mutual recursion (but not nested recursion at the moment).
  Mutual recursion is not too bad, we just need to be careful to call [build_rec]
  with the correct typesym to count.*)
Definition mk_adts (P: poly_map) : mut_in_type -> Set :=
  W mut_in_type P (fun p n => build_base p (a_constrs (proj1_sig n)))
  (fun this i => build_rec P (proj1_sig i) (a_constrs (proj1_sig this))).


(*Constructors*)

(*From a given constructor and the non-recursive data, build the type A*)
Definition get_constr_type (P: poly_map) (a: adt) (cs: list constr) (c: constr)
  (c_in: inb constr_eq_dec c cs)
  (data: build_constr_base P c):
  build_base P cs :=
  build_extra constr_eq_dec (build_in_type constr_eq_dec c_in) data.

(*Note the weird type of [recs]. This says that we have n instances of 
  [mk_adts P t], where n is the number of times t occurs recursively in
  c's constructor list. ([num_rec_type] just lifts n to the type level)
  But we don't just give a list, or an n-tuple/vector, because we need
  to keep track of which index in c's arg list each instance comes from.
  This will be extremely helpful later*)
Definition make_constr (P: poly_map) (a: mut_in_type) (c: constr)
  (c_in: inb constr_eq_dec c (a_constrs (proj1_sig a)))
  (data: build_constr_base P c)
  (recs : forall (t: mut_in_type), 
    num_rec_type (proj1_sig t) (c_args c) -> mk_adts P t) : mk_adts P a :=
  mkW mut_in_type P _ _
  a (get_constr_type P (proj1_sig a) _ c c_in data) recs.

(*Now that the core encoding is finished, we prove some theorems*)

Section Theorems.

(*Inversion: For any instance of [mk_adts], we can find the constructor
  and the arguments used to create it*)

(*No axioms needed*)
Definition find_constr: forall (a: mut_in_type) (P: poly_map) (x: mk_adts P a),
  {c: constr & {t: inb constr_eq_dec c (a_constrs (proj1_sig a)) *
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

Lemma constrs_disjoint: forall (a: mut_in_type) (P: poly_map) 
  (c1 c2: constr) 
  (c1_in: inb constr_eq_dec c1 (a_constrs (proj1_sig a)))
  (c2_in: inb constr_eq_dec c2 (a_constrs (proj1_sig a)))
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
(P: poly_map) (A: poly_map -> I -> Set)
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

(*Relies on UIP*)
Lemma constrs_inj: forall (a: mut_in_type) (P: poly_map) 
(c: constr) 
(c_in: inb constr_eq_dec c (a_constrs (proj1_sig a)))
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
  (P: forall (a: mut_in_type) (p: poly_map), mk_adts p a -> Prop):
  (*For every ADT and every constructor, *)
  (forall (a: mut_in_type) (p: poly_map) (x: mk_adts p a)
    (c: constr) (c_in:  inb constr_eq_dec c (a_constrs (proj1_sig a)))
    (b: build_constr_base p c)
    (recs: forall (t: mut_in_type), 
      num_rec_type (proj1_sig t) (c_args c) -> mk_adts p t)
    (x_eq: x = make_constr p a c c_in b recs),
    (*if whenever P holds on all recursive instances*)
    (forall t r, P t p (recs t r)) ->
    (*then it holds for the constructor*)
    P a p x) ->

(*P holds for all instances of m*)
(forall (a: mut_in_type) (p: poly_map) (x: mk_adts p a), P a p x).
Proof.
  intros IH a p.
  induction x.
  match goal with 
  | |- ?P ?i ?p ?x => remember x as y
  end.
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


(*The full mapping from types to Sets, where ADT instances are interpreted
  as the corresponding [mk_adts]*)
(*NOTE: unlike previous version, domain of ADT is definitionally equal to
  mk_adts, not propositionally equal. This reduces need for casts*)
(*NOTE: will need to fix later to change p to handle non-uniformity*)
(*JOSH - need to modify p here if we want the theorem to hold whenever
  we use types in a different context - otherwise, will not work
  Because we will only use typs for this, only can use previously defined
  so issue with circularity - we will tie the knot by using
  dom_full later - but does this give problems with the proof?
  is it even possible to restrict to non-uniform types?*)
Definition domain (p: poly_map) (t: ty) : Set :=
  match t with
  | ty_app ts tys =>
    (*If ts is in m, then map to appropriate ADT*)
    match (typesym_get_adt ts) with
    | inleft a =>
      mk_adts p (build_in_type adt_eq_dec (proj1' (proj2_sig a)))
    | inright _ => ty_to_set p t
    end
  | _ => ty_to_set p t
  end. 

(*This coincides with [ty_to_set] for all non-recursive types*)
Lemma is_rec_ty_eq {t: ty} (Hrec: is_rec_ty t = false) p:
  domain p t = ty_to_set p t.
Proof.
  destruct t; simpl in *; unfold is_rec_ts in Hrec; auto.
  destruct (typesym_get_adt t); simpl in *; auto.
  discriminate.
Qed.

Lemma is_rec_ty_unit {t: ty} (Hrec: is_rec_ty t) p:
  unit = ty_to_set p t.
Proof.
  destruct t; simpl in *; unfold is_rec_ts in Hrec; try discriminate.
  destruct (typesym_get_adt t); simpl in *; auto.
  discriminate.
Qed.

(*Now convert an [hlist] on [domains] to one on [ty_to_set] (ie: remove
  recursive information)*)
Fixpoint hlist_dom_to_set {p: poly_map} {l: list ty} (h: hlist (domain p) l):
  hlist (ty_to_set p) l.
Proof.
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

(*Two theorems about this: behavior on non-recursive and
  recursive elements*)

(*If the ith element of l is non-recursive,
  [hlist_dom_to_set] is the same as the original list (UIP)*)
Lemma hlist_dom_to_set_ith_nonrec {p: poly_map} {l: list ty} 
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
      * simpl in *. unfold is_rec_ts in Hrec.
        generalize dependent (hlist_hd h).
        simpl.
        destruct (typesym_get_adt t).
        -- discriminate.
        -- intros. uip_subst e. reflexivity.
    + apply IHl; auto.
      apply Arith_prebase.lt_S_n_stt in H; auto.
Qed.

(*And likewise, if the ith element is recursive, [hlist_dom_to_set]
  gives unit*)
Lemma hlist_dom_to_set_ith_rec {p: poly_map} {l: list ty} 
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
      simpl in *. unfold is_rec_ts in Hrec.
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

Definition args_to_constr_base (p: poly_map) (c: constr)
  (a: hlist (domain p) (c_args c)): build_constr_base p c :=
  args_to_constr_base_aux p (c_args c) a.

(*And build the recursive arguments*)

Definition dom_d: forall p, domain p ty_d := fun p =>
  bases_inhab.
Definition ty_set_d: forall p, ty_to_set p ty_d := fun p =>
  bases_inhab.

(*We require that all ADT names are unique*)
(*TODO: change to decidable version*)
Variable adt_names_uniq: NoDup (map a_name (m_adts m)).

Lemma adt_names_eq {a1 a2: adt}:
  inb adt_eq_dec a1 (m_adts m) ->
  inb adt_eq_dec a2 (m_adts m) ->
  a_name a1 = a_name a2 ->
  a1 = a2.
Proof.
  intros a1_in a2_in name_eq.
  apply (@NoDup_map_in _ _ _ _ a1 a2) in adt_names_uniq; auto.
  - apply (ssrbool.elimT (inb_spec _ _ _) a1_in).
  - apply (ssrbool.elimT (inb_spec _ _ _) a2_in).
Qed.

(*This is conceptually simple as well: the [num_rec_type]
  gives us the index of l that has the correct type, so we just
  identify that element of a. There is a bit of work to make the
  types work out and avoid dependent pattern matching errors*)
Definition args_to_ind_base_aux (p: poly_map) (l: list ty)
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
  adt_names_eq (proj1' (proj2_sig s)) (proj2_sig t) aname_eq : proj1_sig s = proj1_sig t).
  intros rep.
  set (t':=build_in_type adt_eq_dec (proj1' (proj2_sig s))).
  set (pack_eq := (proj2' (in_type_eq adt_eq_dec (m_adts m) t' t)) a_eq :
  (build_in_type adt_eq_dec (proj1' (proj2_sig s))) = t).
  exact (scast (f_equal (mk_adts p) pack_eq) rep).
- intros _ f. exact (is_false f).
Defined.

Definition args_to_ind_base (p: poly_map) (c: constr)
  (a: hlist (domain p) (c_args c)):
  forall t: mut_in_type,
    num_rec_type (proj1_sig t) (c_args c) -> mk_adts p t :=
  args_to_ind_base_aux p (c_args c) a.

Definition constr_rep (p: poly_map) (a: mut_in_type) (c: constr)
  (c_in: inb constr_eq_dec c (a_constrs (proj1_sig a)))
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

(*One small result we need relating [typesym_get_adt] and [is_ind_occ]*)
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

(*Generate the [hlist] from the [build_constr_base] and recs*)
Definition constr_ind_to_args_aux (p: poly_map) (l: list ty)
  (b: build_constr_base_aux p l)
  (recs: forall t : mut_in_type, num_rec_type (proj1_sig t) l -> mk_adts p t):
  hlist (domain p) l.
refine (gen_hlist_i (domain p) l ty_d _).
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
case (typesym_get_adt ts).
- intros s Hindocc _.
  (*Have all the info for recs (why we needed Heq)*)
  set (t':= (build_in_type adt_eq_dec (proj1' (proj2_sig s)))).
  set (n:= exist _ i (andb_conj Hi (Hindocc  s eq_refl)) : num_rec_type (proj1_sig t') l).
  exact (recs t' n).
- intros _ _ bse.
  exact bse.
Defined.

Definition constr_ind_to_args (p: poly_map) (c: constr)
  (b: build_constr_base p c)
  (recs: forall t : mut_in_type, num_rec_type (proj1_sig t) (c_args c) -> mk_adts p t):
  hlist (domain p) (c_args c) :=
  constr_ind_to_args_aux p (c_args c) b recs.

(*Before proving the inverse results, we need a few
  lemmas allowing us to simplify [constr_ind_to_args_aux].
  In particular, we prove simplifications for the case when
  (nth i l ty_d) is recursive and non-recursive. These lemmas
  are tricky because we need to generalize (nth i l ty_d) in
  very particular ways*)

Lemma is_ind_occ_domain p (a: mut_in_type) (t: ty) 
  (Hind: is_ind_occ (a_name (proj1_sig a)) t):
  domain p t = mk_adts p a.
Proof.
  unfold is_ind_occ in Hind.
  destruct t; simpl; try solve [apply (is_false Hind)].
  destruct (typesym_get_adt t).
  - f_equal. apply in_type_eq; simpl.
    apply adt_names_eq.
    + apply (proj1' (proj2_sig s)).
    + apply (proj2_sig a).
    + destruct (string_dec _ _); auto. discriminate.
  - apply (is_false Hind).
Qed.

(*One of the main lemmas we need: if the ith element of l is non-recursive,
  the the ith element of the constructed hlist is the same as the
  ith element of the original tuple*)
Lemma constr_ind_to_args_aux_nonrec {p: poly_map} {l: list ty}
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
      unfold is_rec_ts.
      destruct (typesym_get_adt t); try discriminate.
      intros.
      uip_subst e0. reflexivity.
  }
  specialize (H (nth i l ty_d) e).
  simpl in H |- *.
  rewrite H.
  apply scast_eq_uip.
Qed.

(*And the lemma for recursive arguments*)
Lemma constr_ind_to_args_aux_rec {p: poly_map} {l: list ty}
(b: build_constr_base_aux p l)
(recs: forall t, num_rec_type (proj1_sig t) l -> mk_adts p t)
(t: mut_in_type) (x: num_rec_type (proj1_sig t) l):
hnth (proj1_sig x)(constr_ind_to_args_aux p l b recs) ty_d
(dom_d p) =
scast (eq_sym (is_ind_occ_domain p t (nth (proj1_sig x) l ty_d) 
  (proj2_bool (proj2_sig x))))
  (recs t x).
Proof.
  generalize dependent (eq_sym
    (is_ind_occ_domain p t (nth (proj1_sig x) l ty_d)
       (proj2_bool (proj2_sig x)))).
  unfold constr_ind_to_args_aux.
  intros e.
  assert (Hi: Nat.ltb (proj1_sig x) (length l)). {
    exact (proj1_bool (proj2_sig x)).
  }
  rewrite gen_hlist_i_nth with(Hi:=Hi).
  simpl.
  (*Again, we need a more generic lemma*)
  match goal with
  | |- match nth (proj1_sig x) l ty_d as t' in ty return 
    (t' = nth (proj1_sig x) l ty_d -> ty_to_set p t' -> domain p t')
      with
      | ty_base b' => ?aa
      | ty_var v => ?bb
      | ty_app ts tys => ?cc
      end ?f ?g = ?y =>
    assert (forall (t1: ty) (Heq: t1 = nth (proj1_sig x) l ty_d),
      match t1 as t' return (t' = nth (proj1_sig x) l ty_d -> ty_to_set p t' -> domain p t')
      with
      | ty_base b' => aa
      | ty_var v => bb
      | ty_app ts tys => cc
      end Heq 
      (scast (f_equal (ty_to_set p) (eq_sym Heq)) 
    (big_sprod_ith b (proj1_sig x) ty_d (dom_d p))) =
    scast (f_equal (domain p) (eq_sym Heq)) (scast e (recs t x))
    
    )
  end.
  {
    (*Now we can destruct*)
    destruct t1; intros.
    - (*Most cases are contradictions*)
      exfalso.
      destruct x; simpl in *.
      rewrite <- Heq, andb_false_r in i.
      apply (is_false i).
    - exfalso.
      destruct x; simpl in *.
      rewrite <- Heq, andb_false_r in i.
      apply (is_false i).
    - (*Here, we don't care about the [big_sprod] because we are not using it*)
      generalize dependent (typesym_get_adt_ind_occ t0 l0 (nth (proj1_sig x) l ty_d)
      (eq_sym Heq)).
      generalize dependent (scast (f_equal (ty_to_set p) (eq_sym Heq))
      (big_sprod_ith b (proj1_sig x) ty_d (dom_d p))).
      simpl.
      rewrite scast_scast.
      gen_scast.
      (*Now we can destruct*)
      destruct (typesym_get_adt t0) eqn : Hgetadt.
      + intros e0 _ Hind.
        (*Now we just need to prove that these pairs are equal*)
        match goal with 
        |- recs ?t1 ?x1 = scast ?H (recs ?t2 ?x2) =>
          assert (t1 = t2)
        end.
        {
          apply in_type_eq; simpl.
          apply adt_names_eq.
          - apply (proj1' (proj2_sig s)).
          - apply (proj2_sig t).
          - specialize (Hind s eq_refl).
            clear -Heq x Hgetadt.
            destruct x; simpl in *.
            rewrite <- Heq in i. simpl in i.
            rewrite Hgetadt in i.
            destruct (string_dec _ _); auto; simpl in i;
            rewrite andb_false_r in i; apply (is_false i).
        }
        subst.
        (*For some reason, need to do this here, not before,
          or else we get "uncaught exception"*)
        match goal with 
        |- recs ?t1 ?x1 = scast ?H (recs ?t2 ?x2) =>
          replace x1 with x2 by (apply num_rec_type_eq; reflexivity)
        end.
        uip_subst e0.
        reflexivity.
      + (*Contradiction case*)
        intros e0 t1 _.
        exfalso.
        destruct x; simpl in *.
        rewrite <- Heq in i.
        simpl in i.
        rewrite Hgetadt, andb_false_r in i.
        apply (is_false i).
  }
  specialize (H _ eq_refl). simpl in *.
  rewrite H.
  reflexivity.
Qed.

(*Now, the proofs of the inverse:*)
Lemma constr_ind_args_inv_aux1 {p: poly_map} {l: list ty}
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
    rewrite <- (is_rec_ty_unit Hrec).
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


Lemma constr_ind_args_inv_aux2 {p: poly_map} {l: list ty}
(b: build_constr_base_aux p l)
(recs: forall t : mut_in_type, num_rec_type (proj1_sig t) l -> mk_adts p t):
forall t x,
  args_to_ind_base_aux p l (constr_ind_to_args_aux p l b recs) t x =
  recs t x.
Proof.
  intros.
  unfold args_to_ind_base_aux.
  (*Did bulk of work in previous lemma - this lets us destruct
    without dependent type issues*)
  rewrite constr_ind_to_args_aux_rec.
  gen_scast.
  generalize dependent (proj2_bool (proj2_sig x)).
  simpl.
  destruct (nth (proj1_sig x) l ty_d).
  - intros. exact (is_false i).
  - intros. exact (is_false i).
  - simpl. destruct (typesym_get_adt t0).
    + destruct (string_dec (a_name (proj1_sig s)) (a_name (proj1_sig t)));
      try discriminate.
      intros.
      rewrite scast_scast.
      apply scast_refl_uip.
    + intros. exact (is_false i).
Qed.

(*For the other direction, we need to get information out of the
  [is_rec_ty] hypothesis to construct the needed [num_rec_type]*)
Lemma is_rec_ty_get_info {i l} (Hi: i < length l) (Hrec: is_rec_ty (nth i l ty_d)):
  {t: mut_in_type & {x: num_rec_type (proj1_sig t) l | proj1_sig x = i}}.
Proof.
  unfold is_rec_ty in Hrec.
  destruct (nth i l ty_d) eqn : Hnth;
  try solve[apply (is_false Hrec)].
  unfold is_rec_ts in Hrec.
  destruct (typesym_get_adt t) eqn : Hget; try solve[apply (is_false Hrec)].
  destruct s as [a [a_in a_nameq]].
  apply (existT _ (build_in_type adt_eq_dec a_in)).
  simpl.
  assert (Hind: is_ind_occ (a_name a) (nth i l ty_d)). {
    unfold is_ind_occ.
    rewrite Hnth. rewrite Hget.
    simpl. destruct (string_dec _ _); auto.
  }
  assert (Hi': Nat.ltb i (length l)). {
    apply (ssrbool.introT (PeanoNat.Nat.ltb_spec0 i _) Hi).
  }
  set (x := exist _ i (andb_conj Hi' Hind) : num_rec_type a l).
  apply (exist _ x). reflexivity.
Qed.

(*And the third result: the other direction*)
Lemma constr_ind_args_inv_aux3 {p: poly_map} {l: list ty}
(h: hlist (domain p) l):
constr_ind_to_args_aux p l 
  (args_to_constr_base_aux p l h) (args_to_ind_base_aux p l h) = h.
Proof.
  apply hlist_ext_eq with (d:=ty_d)(d':=dom_d p).
  intros i Hi.
  destruct (is_rec_ty (nth i l ty_d)) eqn : Hrec.
  - (*This is a bit trickier because we need to construct the dependent types*)
    destruct (is_rec_ty_get_info Hi Hrec) as [t [x Hix]].
    subst.
    rewrite (constr_ind_to_args_aux_rec _ _ t x).
    generalize dependent (eq_sym
    (is_ind_occ_domain p t (nth (proj1_sig x) l ty_d)
       (proj2_bool (proj2_sig x)))).
    unfold args_to_ind_base_aux.
    generalize dependent (proj2_bool (proj2_sig x)).
    (*Now both sides refer to the same hnth*)
    generalize dependent (hnth (proj1_sig x) h ty_d (dom_d p)).
    (*And so we can destruct*)
    destruct (nth (proj1_sig x) l ty_d); simpl; intros;
    try solve[apply (is_false i)].
    destruct (typesym_get_adt t0); try solve[apply (is_false i)].
    destruct (string_dec (a_name (proj1_sig s)) (a_name (proj1_sig t)));
    try discriminate.
    rewrite scast_scast. apply scast_refl_uip.
  - (*Easier - just use existing lemmas*)
    rewrite (constr_ind_to_args_aux_nonrec _ _ Hi Hrec).
    unfold args_to_constr_base_aux, big_sprod_ith.
    rewrite big_sprod_to_hlist_inv,
    (hlist_dom_to_set_ith_nonrec _ _ _ _ (dom_d p) Hrec Hi), scast_scast.
    apply scast_refl_uip.
Qed.

(*And the corollaries:*)
Corollary constr_ind_args_inv1 {p: poly_map} {c: constr}
(b: build_constr_base p c)
(recs: forall t : mut_in_type, num_rec_type (proj1_sig t) (c_args c) -> mk_adts p t):
args_to_constr_base p c (constr_ind_to_args p c b recs) = b.
Proof.
apply constr_ind_args_inv_aux1.
Qed.

Corollary constr_ind_args_inv2 {p: poly_map} {c: constr}
(b: build_constr_base p c)
(recs: forall t : mut_in_type, num_rec_type (proj1_sig t) (c_args c) -> mk_adts p t):
forall t x,
  args_to_ind_base p c (constr_ind_to_args p c b recs) t x =
  recs t x.
Proof.
apply constr_ind_args_inv_aux2.
Qed.

Lemma constr_ind_args_inv3 {p: poly_map} {c: constr}
(h: hlist (domain p) (c_args c)):
constr_ind_to_args p c 
  (args_to_constr_base p c h) (args_to_ind_base p c h) = h.
Proof.
apply constr_ind_args_inv_aux3.
Qed.

End Inverse.

(*And now the 4 conditions, fully:*)
Section Theorems.

(*Needs funext and UIP*)
Theorem find_constr_rep {p: poly_map} {t: mut_in_type} (x: mk_adts p t):
  {c: constr & {Hf: inb constr_eq_dec c (a_constrs (proj1_sig t)) *
    hlist (domain p) (c_args c) |
    x = constr_rep p t c (fst Hf) (snd Hf)}}.
Proof.
  destruct (find_constr t p x) as [c [[[c_in b] recs] Hx]]; subst.
  apply (existT _ c).
  apply (exist _ (c_in, constr_ind_to_args p c b recs)).
  simpl.
  unfold constr_rep.
  rewrite constr_ind_args_inv1.
  (*Here, we need functional extensionality*)
  f_equal.
  repeat (apply functional_extensionality_dep; intros).
  rewrite constr_ind_args_inv2; reflexivity.
Qed.

(*Axiom-free*)
Theorem constr_rep_disjoint {p: poly_map} {t: mut_in_type} {c1 c2: constr}
  {c1_in: inb constr_eq_dec c1 (a_constrs (proj1_sig t))}
  {c2_in: inb constr_eq_dec c2 (a_constrs (proj1_sig t))}
  (h1: hlist (domain p) (c_args c1))
  (h2: hlist (domain p) (c_args c2)):
  c1 <> c2 ->
  constr_rep p t c1 c1_in h1 <> constr_rep p t c2 c2_in h2.
Proof.
  apply constrs_disjoint.
Qed.

(*One more lemma about [constr_ind_to_args_aux] 
  allowing us to replace recs without requiring funext*)
Lemma constr_ind_to_args_recs_ext {p: poly_map} {l: list ty}
  {b} {recs1 recs2}
  (Hext: forall t x, recs1 t x = recs2 t x):
  constr_ind_to_args_aux p l b recs1 =
  constr_ind_to_args_aux p l b recs2.
Proof.
  apply hlist_ext_eq with(d:=ty_d)(d':=dom_d p).
  intros i Hi.
  set (Hi':=ssrbool.introT (PeanoNat.Nat.ltb_spec0 _ _) Hi :
      Nat.ltb i (Datatypes.length l)).
  unfold constr_ind_to_args_aux.
  rewrite !gen_hlist_i_nth with (Hi:=Hi').
  simpl.
  generalize dependent (big_sprod_ith b i ty_d (dom_d p)).
  intros t.
  (*Again, we need a more generic lemma*)
  match goal with
  | |- (match nth i l ty_d as t1 in ty return (t1 = nth i l ty_d -> ty_to_set p t1 -> domain p t1)
      with
      | ty_base b1 => ?aa
      | ty_var v1 => ?bb
      | ty_app ts1 tys1 => ?cc
      end ?f ?g) = 
      (match nth i l ty_d as t2 in ty return (t2 = nth i l ty_d -> ty_to_set p t2 -> domain p t2)
      with
      | ty_base b2 => ?aaa
      | ty_var v2 => ?bbb
      | ty_app ts2 tys2 => ?ccc
      end ?f ?g)
      =>
    assert (forall (t: ty) (Heq: t = nth i l ty_d),
      (match t as t3 return (t3 = nth i l ty_d -> ty_to_set p t3 -> domain p t3)
      with
      | ty_base b1 => aa
      | ty_var v1 => bb
      | ty_app ts1 tys1 => cc
      end Heq (scast (f_equal (ty_to_set p) (eq_sym Heq)) g)) =
      (match t as t4 return (t4 = nth i l ty_d -> ty_to_set p t4 -> domain p t4)
      with
      | ty_base b2 => aaa
      | ty_var v2 => bbb
      | ty_app ts2 tys2 => ccc
      end Heq (scast (f_equal (ty_to_set p) (eq_sym Heq)) g)))
  end.
  {
    (*The proof is easy if we generalize appropriately*)
    destruct t0; auto.
    intros Heq.
    generalize dependent (typesym_get_adt_ind_occ t0 l0 (nth i l ty_d) (eq_sym Heq)).
    generalize dependent (scast (f_equal (ty_to_set p) (eq_sym Heq)) t).
    simpl.
    destruct (typesym_get_adt t0); auto.
  }
  specialize (H _ eq_refl); simpl in H.
  apply H.
Qed.
  
(*Requires UIP*)
Theorem constr_rep_inj {p: poly_map} {t: mut_in_type}  {c: constr}
  {c_in: inb constr_eq_dec c (a_constrs (proj1_sig t))}
  (h1 h2: hlist (domain p) (c_args c)):
  constr_rep p t c c_in h1 = constr_rep p t c c_in h2 ->
  h1 = h2.
Proof.
  intros Hrepeq.
  apply constrs_inj in Hrepeq.
  destruct Hrepeq as [Hargs Hrec].
  rewrite <- constr_ind_args_inv3 with (h:=h1),
  <- constr_ind_args_inv3 with (h:=h2).
  rewrite Hargs.
  apply constr_ind_to_args_recs_ext.
  assumption.
Qed.

Lemma is_ind_occ_twice {a1 a2: mut_in_type} (t: ty):
  is_ind_occ (a_name (proj1_sig a1)) t ->
  is_ind_occ (a_name (proj1_sig a2)) t ->
  a1 = a2.
Proof.
  intros Hind1 Hind2.
  apply in_type_eq.
  apply adt_names_eq.
  - apply (proj2_sig a1).
  - apply (proj2_sig a2).
  - unfold is_ind_occ in *.
    destruct t; try discriminate.
    destruct (typesym_get_adt t); try discriminate.
    destruct (string_dec _ _); try discriminate.
    destruct (string_dec _ _); try discriminate.
    congruence.
Qed.

(*Induction - requires funext and UIP*)
Theorem adt_rep_ind (P: forall (t: mut_in_type) (p: poly_map), mk_adts p t -> Prop):
  (forall (t: mut_in_type) (p: poly_map) (x: mk_adts p t)
    (c: constr) (c_in:  inb constr_eq_dec c (a_constrs (proj1_sig t)))
    (h: hlist (domain p) (c_args c))
    (Hx: x = constr_rep p t c c_in h),
    (forall i (t': mut_in_type) 
      (Hind: is_ind_occ (a_name (proj1_sig t')) (nth i (c_args c) ty_d)), 
       i < length (c_args c) ->
       (*If nth i a has type adt_rep ..., then P holds of it*)
       P t' p (scast (is_ind_occ_domain _ _ _ Hind) 
       (hnth i h ty_d (dom_d p))) 
    ) ->
    P t p x
  ) ->
  forall (a: mut_in_type) (p: poly_map) (x: mk_adts p a), P a p x.
Proof.
  intros Hind a p x.
  apply w_induction.
  intros.
  apply (Hind _ _ _ c c_in (constr_ind_to_args _ c b recs)).
  - subst. unfold constr_rep.
    rewrite constr_ind_args_inv1.
    f_equal.
    repeat(apply functional_extensionality_dep; intros).
    symmetry. apply constr_ind_args_inv2.
  - intros.
    (*Build the [num_rec_type] and apply the other IH*)
    specialize (H t').
    generalize dependent (is_ind_occ_domain p0 t' (nth i (c_args c) ty_d) Hind0).
    assert (Hrec:=ind_occ_is_rec_ty Hind0).
    destruct (is_rec_ty_get_info H0 Hrec) as [t1 [y Hiy]]. subst i.
    intros e.
    unfold constr_ind_to_args.
    rewrite constr_ind_to_args_aux_rec.
    rewrite scast_scast.
    assert (t' = t1). {
      apply (is_ind_occ_twice  (nth (proj1_sig y) (c_args c) ty_d)); auto.
      clear -y.
      destruct y; simpl. 
      apply (proj2_bool i).
    }
    subst.
    specialize (H y).
    rewrite scast_refl_uip.
    apply H.
Qed.


(*Another version of induction for uniform parameters
  Not hard to prove, but we need a clever use of impredicativity to 
  get the right IH*)
Theorem adt_rep_ind_unif (p: poly_map) (P: forall (t: mut_in_type), mk_adts p t -> Prop):
  (forall (t: mut_in_type) (x: mk_adts p t)
    (c: constr) (c_in:  inb constr_eq_dec c (a_constrs (proj1_sig t)))
    (h: hlist (domain p) (c_args c))
    (Hx: x = constr_rep p t c c_in h),
    (forall i (t': mut_in_type) 
      (Hind: is_ind_occ (a_name (proj1_sig t')) (nth i (c_args c) ty_d)), 
       i < length (c_args c) ->
       (*If nth i a has type adt_rep ..., then P holds of it*)
       P t' (scast (is_ind_occ_domain _ _ _ Hind) 
       (hnth i h ty_d (dom_d p))) 
    ) ->
    P t x
  ) ->
  forall (a: mut_in_type) (x: mk_adts p a), P a x.
Proof.
  intros Hind a x.
  pose proof (adt_rep_ind 
    (fun (t: mut_in_type) (p: poly_map) (y: mk_adts p t) =>
    (forall (P: forall t, mk_adts p t -> Prop),
      (forall (t: mut_in_type) (x: mk_adts p t)
      (c: constr) (c_in:  inb constr_eq_dec c (a_constrs (proj1_sig t)))
      (h: hlist (domain p) (c_args c))
      (Hx: x = constr_rep p t c c_in h),
      (forall i (t': mut_in_type) 
        (Hind: is_ind_occ (a_name (proj1_sig t')) (nth i (c_args c) ty_d)), 
        i < length (c_args c) ->
        (*If nth i a has type adt_rep ..., then P holds of it*)
        P t' (scast (is_ind_occ_domain _ _ _ Hind) 
        (hnth i h ty_d (dom_d p))) 
      ) ->
      P t x) ->
    P t y))).
  simpl in H. apply H;
  clear H; intros.
  - eapply H0.
    apply Hx.
    intros. apply H; auto.
  - eapply Hind.
    apply Hx. auto.
Qed. 

(*Version for non-mutual types*)
Lemma non_mut_eq (Hm: Nat.eqb (length (m_adts m)) 1) (t1 t2: mut_in_type):
  t1 = t2.
Proof.
  destruct t1; destruct t2; simpl in *.
  assert (x = x0). {
    destruct (m_adts m); simpl in *; try discriminate.
    destruct l; simpl in *; try discriminate.
    do 2 (destruct adt_eq_dec; subst; auto; try discriminate).
  }
  subst.
  assert (i = i0) by apply bool_irrelevance.
  subst. reflexivity.
Qed.

(*First, do uniform one - see if we need non-uniform*)
Theorem adt_rep_ind_single (Hm: Nat.eqb (length (m_adts m)) 1) 
  (p: poly_map) (t: mut_in_type) 
  (P: mk_adts p t -> Prop):
  (forall (x: mk_adts p t)
    (c: constr) (c_in:  inb constr_eq_dec c (a_constrs (proj1_sig t)))
    (h: hlist (domain p) (c_args c))
    (Hx: x = constr_rep p t c c_in h),
    (forall i
      (Hind: is_ind_occ (a_name (proj1_sig t)) (nth i (c_args c) ty_d)), 
       i < length (c_args c) ->
       (*If nth i a has type adt_rep ..., then P holds of it*)
       P (scast (is_ind_occ_domain _ _ _ Hind) 
       (hnth i h ty_d (dom_d p))) 
    ) ->
    P x
  ) ->
  forall (x: mk_adts p t), P x.
Proof.
  intros IH.
  (*Need a cast from equality*)
  pose proof (adt_rep_ind_unif p (fun t x =>
    P (scast (f_equal (mk_adts p) (non_mut_eq Hm _ _)) x))) as Hind.
  intros x.
  (*Now we need an scast*)
  rewrite <- (scast_eq_sym' (f_equal (mk_adts p) (non_mut_eq Hm t _)) x).
  apply Hind; clear Hind.
  intros.
  assert (t0 = t). {
    apply (non_mut_eq Hm).
  }
  subst.
  apply (IH _ c c_in h).
  - rewrite scast_refl_uip. reflexivity.
  - intros.
    specialize (H i t Hind H0).
    revert H.
    rewrite scast_scast.
    do 2 (gen_scast; intros).
    assert (e = e0) by apply UIP.
    subst. auto.
Qed.

End Theorems.

End Encode.

(*Handle multiple ADTs in context*)
Section Context.

Definition ctx := list mut.

(*Build up [typs]*)

(*TODO: use existing/fix*)
Definition map_from_list {A B: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) 
  (d: A -> B) (l: list (A * B)) (x: A) : B :=
  fold_right (fun y acc => if eq_dec (fst y) x then (snd y) else acc) (d x) l.

Definition build_poly_map (p: poly_map) (l: list typevar) (l2: list Set) :=
  map_from_list typevar_dec p (combine l l2).

Definition ts_find_mut (t: typesym) (c: ctx) : option mut :=
  fold_right (fun m acc => if is_rec_ts m t then Some m else acc) None c.

Lemma ts_find_mut_some t c m:
  ts_find_mut t c = Some m ->
  is_rec_ts m t /\ inb mut_eq_dec m c.
Proof.
  induction c; simpl; try discriminate.
  destruct (is_rec_ts a t) eqn : Hrec.
  - intros C; inversion C; subst. destruct mut_eq_dec; auto.
  - intros Hmut. apply IHc in Hmut.
    destruct Hmut as [Hr Hinb]; rewrite Hr, Hinb, orb_true_r; auto.
Qed. 

(*Question: should we just do this in a context?
  and define domain based on the context?
  that might be the way to go, honestly
  current definitions are special case with 1 mutual type
  should try that and see - would avoid this issue
  problem is that ty_to_set defined for single mut (because we need
  to tie the knot somewhow)
  could do as before and just axiomatize domain but that is not great

  but this means that typs actually does need to account for recursive
  types (for previously declared)
  this is trickier than i thought

  domain 

  *)

(*Does this work? Why is there no recursion?
  I think: we have to modify p
  
  Ex dom_full c (fun _ _ => empty) p (list (list unit))
  gives mk_adts typs (list_mut) p (list_adt)
  completely ignores tys
  should be:
  p maps (ts_args ts) to (map (dom_full c typs p) tys)

  do ex:
  mk_adts typs list_mut (a -> dom_full c tys p (list unit))
  mk_adts typs list_mut (a -> mk_adts typs list_mut (a -> unit))

  *)

(*Ah, but the problem is that we cannot map - is it OK to use [domain] here?
  No, we need domain with [typs_full]
  ex: list (tree int) or whatever - when evaluating list, we need tree to be
  evaluated correctly

  so we need to iterate - rely on only using things before unforunately
  *)

(*It is extremely tricky to deal with an entire context of types.
  While we do not (yet) handle nested recursive types, we could have
  a non-recursive constructor that uses a previously declared ADT,
  and these can be nested (including with abstract types).
  For example, we can have
  data bar A (abstract)
  data foo A = | fst of (list (list unit)) | snd of (list (bar unit))

  How should the [typs] function work?
  Clearly we want to send each ADT to its [domain] (i.e. mk_adts)
  but mk_adts depends on the poly_map p.
  Whenever we see ts_app ts tys of mutual type (m, a), 
  we should therefore return
  mk_adts tys p m a, where p maps (ts_args ts) to the evaluation of tys.
  But what is this evaluation? [tys] may also include ADTs, and so on.

  In the example above, we should interpret list (list unit) as
  mk_adts tys list_m ('a -> mk_adts tys list_m ('a -> unit) list_a) list_a
  As we can see, the process of constructing p is recursive, and it must
  eventually hit a base type/empty list. So we have a separate recursive
  function to build this p, which is the difficult part
*)

Fixpoint build_p (c: ctx) (p: poly_map) (typs: typesym -> list ty -> Set) 
  (t: ty) : Set :=
  match t with
  | ty_app ts tys =>
    match (ts_find_mut ts c) with
    | Some m =>
        match (typesym_get_adt m ts) with
        | inleft a =>
          let newp := build_poly_map p (ts_args ts) (map (build_p c p typs) tys) in
          (*let p := build_poly_map (ts_args ts) (map (domain acc m p) tys) in*)
          (*mk_adts?*)
          mk_adts typs m newp (build_in_type adt_eq_dec (proj1' (proj2_sig a)))
          (*domain (typs_full c p (*buildP?*)) m (build_p p)  
          mk_adts acc m p (build_in_type adt_eq_dec (proj1' (proj2_sig a)))*)
        | inright _ => typs ts tys
        end 
      | None => typs ts tys
      end
  | ty_base b => bases b
  | ty_var v => p v
  end.

(*TODO: may need to change this see*)
Fixpoint typs_full (c: ctx) (p: poly_map) (typs: typesym -> list ty -> Set) {struct c}
  : typesym -> list ty -> Set :=
    match c with
    | nil => typs
    | m :: ms =>
      
      (*aha, this is the key: everything in ms is set correctly in mk_adts,
        and m doesnt matter because it is recursive!*)
        (* fun ts tys => build_p c (typs_full ms p typs) (ty_app ts tys) *)
        (*Don't know if this is better*)
        (*Maybe we do want build_p to take in ms - it should not matter
          (i.e. we will have to prove that it doesn't matter)
          but will make proofs easier*)


      let acc := typs_full ms p typs in 
      fun ts tys =>
        match (typesym_get_adt m ts) with
        | inleft a =>
          (*Should not be build_poly_map here by uniformity*)
          let p' := build_poly_map p (ts_args ts) (map (build_p ms p acc) tys) in
          mk_adts acc m p' (build_in_type adt_eq_dec (proj1' (proj2_sig a)))
        | inright _ =>
           acc ts tys
        end 
    end.

(*Lemma typs_full_change (c1 c2: ctx) (p: poly_map) (typs: typesym -> list ty -> Set):*)

Ltac funext :=
  repeat (apply functional_extensionality_dep; intros).
Print build_base.
Print in_type_extra.
Lemma W_change (I: Set) (p: poly_map) (A1 A2: poly_map -> I -> Set)
  (B1: forall i, I -> A1 p i -> Set) (B2: forall i, I -> A2 p i -> Set)
  (i: I)
  (Ha: forall p i, A1 p i = A2 p i)
  (Hb: forall i j (x: A1 p i) (x2: A2 p i),
    (forall Heq, x = scast Heq x2) ->
  B1 i j x = B2 i j x2):
  W I p A1 B1 i = W I p A2 B2 i.
Proof.
  assert (A1 = A2) by (funext; apply Ha).
  subst.
  f_equal.
  funext.
  apply Hb.
  intros. rewrite scast_refl_uip.
  reflexivity.
Qed.
(*  rewrite Hb.
  f_equal.
  apply scast_refl_uip.
Qed.*)


(*TODO: move*)
Lemma in_type_extra_change_f {T : Set} (T_dec : forall x y : T, {x = y} + {x <> y}) 
{l : list T} {f1 f2 : T -> Set}
(*TODO: can we only require on list?*)
(*(Heq: forall x, inb T_dec x l -> f1 x = f2 x)*)
(Heq: forall x, f1 x = f2 x)
:
in_type_extra T_dec l f1 = in_type_extra T_dec l f2.
Proof.
assert (f1 = f2). {
  funext. auto.
}
subst. reflexivity.
Qed.



Lemma ty_to_set_change_typs (tys1 tys2: typesym -> list ty -> Set)
  (m: mut) (p: poly_map) (t: ty)
  (Heq: forall ts tys, ~ is_rec_ts m ts -> tys1 ts tys = tys2 ts tys):
  ty_to_set tys1 m p t = ty_to_set tys2 m p t.
Proof.
  destruct t; simpl; auto.
  unfold is_rec_ts in Heq.
  specialize (Heq t l).
  destruct (typesym_get_adt m t); auto.
Qed.


Definition bool_typ {A: Set} (P: A -> bool) : Set :=
  {x : A | P x}.

Lemma bool_typ_eq {A: Set} (P1 P2: A -> bool) (Heq: forall a, P1 a = P2 a):
  bool_typ P1 = bool_typ P2.
Proof.
f_equal.
funext. auto.
Qed.

Lemma mk_adts_change_typs (tys1 tys2: typesym -> list ty -> Set) (m: mut)
  (p: poly_map) (t: mut_in_type m)
  (Heq: forall ts tys, ~ is_rec_ts m ts -> tys1 ts tys = tys2 ts tys):
  mk_adts tys1 m p t = mk_adts tys2 m p t.
Proof.
  unfold mk_adts.
  assert (Hconstrbase: forall (p: poly_map) (x : constr),
  build_constr_base tys1 m p x =
  build_constr_base tys2 m p x).
  {
    intros.
    unfold build_constr_base, build_constr_base_aux.
    induction (c_args x); simpl; auto.
    rewrite ty_to_set_change_typs with (tys2:=tys2); auto.
    rewrite IHl. reflexivity.
  }
  assert (Hbase: forall (p0 : poly_map) (i : mut_in_type m),
  build_base tys1 m p0 (a_constrs (proj1_sig i)) =
  build_base tys2 m p0 (a_constrs (proj1_sig i))).
  {
    intros.
    unfold build_base.
    apply in_type_extra_change_f. auto.
  }
  apply W_change.
  apply Hbase.
  intros i.
  unfold build_rec.
  unfold num_rec_type.
  intros.
  apply bool_typ_eq.
  intros.
  (*Need to transform cast to [eq_refl]*)
  assert (build_constr_base tys2 m p = build_constr_base tys1 m p) by
    (funext; auto).
  unfold build_base in *.
  generalize dependent x2.
  rewrite H0.
  intros.
  specialize (H eq_refl). subst. reflexivity.
Qed.

(*I think we are going to need an ordering, and the above may work with
  an ordering.
  Basically, suppose we have:
  list A = | nil | cons of (tree A)

  and (non-mut)
  tree A = | leaf | node of (list A)

  Then we cannot construct an interpretation of A without already assigning
  an interp for tree, and vice versa - we will have a series of approximations
  and no gauarntee of convergence

  So the plan is: 
  1. define ordering on context
  2. use [typs_full], which populates each context in order
  3. close the knot by proving that if typs agrees on all typesyms present
    in type, then equal, and using ordering to show that future ones don't impact
  *)

(*NOTE: we need a positivity restriction on types (even without functions).
  We CANNOT have the type (for example)*)

(*When does an ADT a occur non-positively in type t?*)
(*We don't need to implement the whole check, just for now
  check that the above situation does not occur*)
Fixpoint name_in (n: string) (t: ty) : bool :=
  match t with
  | ty_app ts tys => String.eqb (ts_name ts) n || 
    existsb (name_in n) tys
  | _ => false
  end.

Definition adt_nonpos (a: adt) (t: ty) : bool :=
  match t with
  | ty_app ts tys => implb (String.eqb (ts_name ts) (a_name a))
    (forallb (fun x => negb (name_in (a_name a) x)) tys)
  | _ => true
  end.

  (*TODO: bool, better*)
(*Definition nonpos (m: mut) (a: adt) (ts: typesym) (tys: list ty): Prop :=
  inb adt_eq_dec a (m_adts m) ->
  ts_name ts = a_name a ->
  forall (a': adt) (a_in': inb adt_eq_dec a (m_adts m)) (tys: list ty), 
    adt_nonpos a 

  ts_name ts = a_name a -> forall (a': adt)*)


Lemma typs_full_adt (c: ctx) (p: poly_map) (typs: typesym -> list ty -> Set)
  (ts: typesym) (tys: list ty) (m: mut) (a: adt)
  (m_in: inb mut_eq_dec m c) (a_in: inb adt_eq_dec a (m_adts m))
  (ts_eq: ts_name ts = a_name a)
  (tys_pos: forall (a: adt) (a_in: inb adt_eq_dec a (m_adts m)) (t: ty)
    (t_in: inb ty_eq_dec t tys),
    adt_nonpos a t):
  typs_full c p typs ts tys =
  mk_adts (typs_full c p typs) m 
    (build_poly_map p (ts_args ts)
      (map (build_p c p (typs_full c p typs)) tys))
    (build_in_type adt_eq_dec a_in).
Proof.
  (*This won't work but let's see*)
  induction c.
  - simpl in *. discriminate.
  - simpl in m_in.
    destruct mut_eq_dec.
    + subst a0. simpl in m_in.
      rewrite mk_adts_change_typs with (tys2:=typs_full c p typs).
      2: {
        intros. simpl.
        unfold is_rec_ts in H.
        destruct (typesym_get_adt m ts0); auto; contradiction.
      }
      simpl typs_full at 1.
      destruct (typesym_get_adt m ts).
      2: {
        exfalso.
        exact (n _ a_in ts_eq).
      }
      (*So we need to show that these p maps are equal*)
      f_equal.
      * (*So here, by positivity, m cannot affect meaning of tys,
          so we will show that we can safely replace these (TODO)*)
        f_equal.
        (*Lemmas we need
          1. If c1 and c2 agree on all mutual types
            found inside type ty, then build_p is equal
          2. If typs1 and typs2 agree on all nonrec types
            (maybe) in ty, then can switch in build_p
            (not sure about this one)*)
        admit.
      * apply in_type_eq. simpl.
        (*relies on well-formed context*) admit.
    + simpl in m_in.
      simpl typs_full at 1.
      destruct (typesym_get_adt a0 ts).
      {
        (*contradiction becaues cant be in 2 mut at once*)
        admit.
      }
      (*We still have a problem: what if context is 
      list, foo A = g of A * (list unit)
      and then we look at list (foo nat)
      we cannot assume well-ordering here
      we are proving something too strong I think
      TODO: see*)
      rewrite mk_adts_change_typs with (tys2:=typs_full c p typs).
      2: {
        intros.
        simpl.
        unfold
      }
      rewrite (IHc m_in).
      
      simpl in typs_full at 1.
      (*Here, by well-ordering, NOTHING in *)
Admitted.
(* 
      2: apply in_type_eq; simpl.
      simpl.


      Search mk_adts.
    
    
    subst.
  
  
  simpl in *.

  
  
  simpl typs_full. simpl in *.

  simpl.
  (*Or maybe mk_adts*)
  build_p c p (typs_full c p typs) (ty_app ts tys).
Proof.
  simpl.
  assert (ts_find_mut ts c = Some m) by admit.
  rewrite H.
  destruct (typesym_get_adt m ts) eqn : Hget; auto.
  destruct s as [a1 [a1_in a1_name]]; simpl in *.
  assert (a = a1) by admit. subst.
  assert (a1_in = a_in) by apply bool_irrelevance. subst.
  (*This is really the lemma we want - maybe just change it*)
  clear Hget a1_name.
  induction c as [| mhd ctl IH]; [discriminate|].
  simpl in m_in.
  destruct mut_eq_dec; simpl in m_in; subst.
  - simpl typs_full at 1.
    destruct (typesym_get_adt mhd ts) eqn : Hget.
    + destruct s as [a2 [a2_in a2_name]].
      clear Hget.
      assert (a1 = a2) by admit. subst.
      simpl proj1'.
      assert (a2_in = a_in) by apply bool_irrelevance.
      subst. assert (a2_name = ts_eq). apply UIP_dec. apply string_dec.
      subst. 
      (*So here is where we need to prove this stuff*)
      (*First, we change [typs_full] to remove the extra context because
        it does not affect non-adts*)
      rewrite mk_adts_change_typs with (tys1:=(typs_full (mhd :: ctl) p typs))
        (tys2:=((typs_full ctl p typs))).
      2: {
        intros. simpl.
        unfold is_rec_ts in H0.
        destruct (typesym_get_adt mhd ts0); auto.
        contradiction.
      }
      (*Is this true? Need to make sure
        Does this not work if something tys contains something in mhd?
        Ugh need to see*)
      (*Next step: prove result for [build_p]
        2 parts: 
        1. prove that we can change typs in build_p 
          as long as they agree on all *)
      
      string_eq_dec. apply bool_irrelevance. clear a2_name.
  
  simpl. 

  
  
  clear a1_name.




  (*Ideas
  1. prove that [typs_full] is ONLY affected by adts in context, everything else
    equal to tys
  2. prove that we can change typs in [mk_adts] as long as it agrees on
    all typesyms in mutual adt (will be casting, funext, etc)
  3. prove in [build_poly_map] that we can change context as long as all mutual
    types in the argument type are in both
    (basically build_p c1 tys1 ty = build_p c2 tys2 ty 
    if c1 and c2 agree on all muts in ty
    and tys1 and tys2 agree on all typesyms in ty)
  4. then we should be able to prove this lemma by induction on c
    *)
Admitted.*)
  (*destruct (typesym_get_adt)
(*Need to think about how to prove this because just induction on c
  not good idea*)
  induction c; simpl; auto.
  simpl in m_in.
  destruct mut_eq_dec; simpl in *; subst.
  - clear IHc.
    unfold is_rec_ts.
    destruct (typesym_get_adt a0 ts) eqn : Hget.
    + rewrite Hget.
      unfold typs_full at 1.


  mk_adts (typs_full c p typs) 
  
  
  typs ts tys.
*)
(*AHA, this isn't even strictly positive*)
Fail Inductive foo : Type -> Type :=
  | foot: forall (A: Type), foo (foo A) -> foo A.

(*I think: for lemma we want restriction that m occurs uniformly in t
  and this will be true for constructor args (by assumptions)
  Do we need uniformity or just no nesting (which can be ruled out by
    strict positivity?)
  *)
(*No, dont want to adjust p
  ex: if I am interpreteing list(list (unit * a)), have single map
    mapping a to something, stull want to interpret as this
  is the problem in [domain] - maybe because we do actually want
  to adjust p
  let's see if that helps*)

Definition dom_full (c: ctx) (p: poly_map) (tys: typesym -> list ty -> Set)
  (t: ty) : Set :=
  build_p c p (typs_full c p tys) t.

(*2 lemmas*)
Print typs_full.
(*easy*)
Lemma dom_full_adt (c: ctx) (p: poly_map) (typs: typesym -> list ty -> Set)
  (m: mut) (m_in: inb mut_eq_dec m c) (a: adt) (a_in: inb adt_eq_dec a (m_adts m))
  (ts: typesym) (ts_eq: ts_name ts = a_name a) (tys: list ty):
  dom_full c p typs (ty_app ts tys) =
  domain (typs_full c p typs) m 
    (build_poly_map p (ts_args ts) (map (build_p c p (typs_full c p typs)) 
      tys)) (ty_app ts tys)
    (*todo: maybe typs should be typs_full either way ok*).
Proof.
  unfold dom_full.
  simpl.
  assert (Hfindm: ts_find_mut ts c = Some m) by admit.
  rewrite Hfindm.
  destruct (typesym_get_adt m ts); auto.
Admitted.

(*Can we prove this without funext?*)
(*Lemma ty_to_set_change_p typs m p1 p2 t:
(forall x, p1 x = p2 x) ->
ty_to_set typs m p1 t = ty_to_set typs m p2 t.
Proof.
intros Heq.
destruct t; simpl; auto.
Qed.

Lemma domain_change_p typs m p1 p2 t:
  (forall x, p1 x = p2 x) ->
  domain typs m p1 t = domain typs m p2 t.
Proof.
  intros Heq.
  unfold domain. destruct t; auto.
  - apply ty_to_set_change_p; auto.
  - destruct (typesym_get_adt m t); auto.
    Check mk_adts.*)


(*Corollary: if tys = map ty_var (ts_args ts), then we can replace
  build_poly_map ... with p*)
Lemma dom_full_adt_unif (c: ctx) (p: poly_map) (typs: typesym -> list ty -> Set)
(m: mut) (m_in: inb mut_eq_dec m c) (a: adt) (a_in: inb adt_eq_dec a (m_adts m))
(ts: typesym) (ts_eq: ts_name ts = a_name a):
dom_full c p typs (ty_app ts (map ty_var (ts_args ts))) =
domain (typs_full c p typs) m p (ty_app ts (map ty_var (ts_args ts))).
Proof.
  rewrite dom_full_adt with (m:=m)(a:=a); auto.
  f_equal.
  rewrite map_map. simpl.
  (*Need funext unfortunately*)
  funext.
  (*TODO: separate lemma?*)
  unfold build_poly_map.
  induction (ts_args ts); simpl; auto.
  destruct (typevar_dec a0 x); subst; auto.
Qed.

(*TODO: one more that just leaves it generic and gives unif maybe or not*)

(*The harder case*)
Lemma dom_full_non_adt (c: ctx) (p: poly_map) (tys: typesym -> list ty -> Set)
(m: mut) (m_in: inb mut_eq_dec m c) (t: ty)
(Hnty: forall (a: adt) (a_in: inb adt_eq_dec a (m_adts m)) (ts: typesym)
  (ts_eq: ts_name ts = a_name a) (tys: list ty), t <> ty_app ts tys):
dom_full c p tys t = domain (typs_full c p tys) m p t.
Proof.
  unfold dom_full.
  destruct t; simpl; auto.
  destruct (ts_find_mut t c) as [m1|] eqn : Hfindmut.
  2: {
    destruct (typesym_get_adt m t); auto.
    (*TODO: contradiction*)
    admit.
  }
  (*Here, show m1 <> m, first is inleft, second is inright
    and will need to prove result about typs_full for sure*)
  apply ts_find_mut_some in Hfindmut.
  destruct Hfindmut as [t_rec m1_in].
  unfold is_rec_ts in t_rec.
  destruct (typesym_get_adt m1 t); try discriminate.
  clear t_rec.
  (*So t = a(ts) for a in m1 (which cannot be m)*)
  destruct (typesym_get_adt m t).
  - (*Contradiction: contracts Hnty*)
    exfalso.
    exact (Hnty (proj1_sig s0) (proj1 (proj2_sig s0))
      t (proj2 (proj2_sig s0)) l eq_refl).
  - (*Here, need to know about [typs_full]*)
    rewrite typs_full_adt with (m:=m1)(a:=proj1_sig s)(a_in:=proj1'(proj2_sig s)); auto.
    apply (proj2_sig s).


  Search ts_find_mut.
  assert (m <> m1) by admit.

   

Lemma build_p_dom (c: ctx) (p: poly_map) (tys: typesym -> list ty -> Set)
(m: mut) (m_in: inb mut_eq_dec m c) (t: ty):
dom_full c p tys t = domain (typs_full c p tys) m p t.

(*Maybe we need to modify p to be full?*)
Lemma build_p_dom (c: ctx) (p: poly_map) (tys: typesym -> list ty -> Set)
(m: mut) (m_in: inb mut_eq_dec m c) (t: ty):
dom_full c p tys t = domain (typs_full c p tys) m p t.
Proof.
unfold dom_full.
destruct t; simpl; auto.
destruct (ts_find_mut t c) as [m1 |] eqn : Hfindmut.
- pose proof (ts_find_mut_some _ _ _ Hfindmut). 
  destruct H as [Hrecm1 m1_in].
  unfold is_rec_ts in Hrecm1.
  destruct (typesym_get_adt m1 t) eqn : Hget1;
  [|discriminate].
  destruct (typesym_get_adt m t) eqn : Hget.
  * destruct s as [a1 [a1_in a1_name]].
    destruct s0 as [a [a_in a_name]]. 
    simpl in *. 
    assert (m1 = m /\ a1 = a). admit.
    destruct H; subst.
    assert (a_in = a1_in) by apply bool_irrelevance.
    subst.
    
    (*TODO: from uniformity*)
    assert (l = map ty_var (ts_args t)) by admit.
    subst.
    rewrite map_map.
    unfold build_poly_map. simpl.
    assert ( (map_from_list typevar_dec empty
    (combine (ts_args t)
       (map (fun x : typevar => p x) (ts_args t)))) = p) by admit.
    rewrite <- H at 3.
    reflexivity.
  * (*TODO: start here (and earlier) see what we need*)
    rewrite typs_full_adt with (m:=m1)(a:=(proj1_sig s)); auto.
    simpl.
    rewrite Hfindmut.
    rewrite Hget1. auto.
    apply (proj2_sig s).
    apply (proj2_sig s).
  - destruct (typesym_get_adt m t) eqn : Hget; auto.
    (*contradiction*) admit.
    + auto.
    rewrite Hget.
    unfold build_p.
    unfold typs_full at 3. simpl.
  
  
  unfold typs_full at 3.
    simpl. rewrite Hfindmut.
    rewrite Hget1.

End Context.
End ADT.

Arguments ty_base {typevar} {base}. 
Arguments ty_var {typevar base}.
Arguments ty_app {typevar base}. 
