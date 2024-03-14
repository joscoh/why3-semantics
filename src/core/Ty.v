Require Import Wstdlib.
Require Import Ident.
Require Number.
Require Hashcons Weakhtbl. 
Require Import stdpp.base.
Require Import Coq.Wellfounded.Inverse_Image.

Record tvsymbol := {
  tv_name : ident
}.

Definition tvsymbol_eqb (t1 t2: tvsymbol) : bool :=
  ident_eqb t1.(tv_name) t2.(tv_name).

Lemma tvsymbol_eqb_eq (t1 t2: tvsymbol): t1 = t2 <-> 
  tvsymbol_eqb t1 t2.
Proof.
  unfold tvsymbol_eqb.
  rewrite <- ident_eqb_eq.
  destruct t1 as [t1]; destruct t2 as [t2]; simpl; solve_eqb_eq. 
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
  ctr_bnd (fun i => ctr_ret {|tv_name := i|}) (id_register n).

(*In OCaml, this is a stateful function that stores variables
  in hash table and looks up to see if any have been
  created with same name already.
  Here, we just give a new one - NOTE: is this a problem?*)
Definition tv_of_string (s: string) : ctr tvsymbol :=
  create_tvsymbol (id_fresh s).

(** Type Symbols and Types **)
Unset Elimination Schemes.

(*Here is the first of several places where we have different
  types between Coq and OCaml. In Coq we use a mutually recursive
  Inductive; in OCaml, we have a mutually recursive mix of 
  Records and recursive types. This is for compatibility with
  existing OCaml code; Coq does not support this natively.
  We name the Coq types with a _c suffix, the OCaml ones with
  a _o suffix, and keep the extracted names the same as the
  existing API*)

Inductive type_def (A: Type) : Type :=
  | NoDef
  | Alias: A -> type_def A
  | Range: Number.int_range -> type_def A
  | Float: Number.float_format -> type_def A.

Arguments NoDef {_}.
Arguments Alias {_}.
Arguments Range {_}.
Arguments Float {_}.

Record ty_o (A: Type) := 
  mk_ty_o { ty_node: A;
    ty_tag: Weakhtbl.tag}.
    
Record tysymbol_o (A: Type) := mk_ts_o {
  ts_name : ident;
  ts_args : list tvsymbol;
  ts_def : type_def A
}.

(*Coq types - we append with _c for coq*)
Inductive ty_c : Type :=
  | mk_ty_c : ty_node_c -> Weakhtbl.tag -> ty_c
with tysymbol_c : Type :=
  | mk_ts_c : ident -> list tvsymbol -> type_def ty_c -> tysymbol_c
with ty_node_c : Type :=
  | Tyvar : tvsymbol -> ty_node_c
  | Tyapp: tysymbol_c -> list ty_c -> ty_node_c.

(*OCaml names for extraction*)
Definition ty := ty_o ty_node_c.
Definition tysymbol := tysymbol_o ty.

(*To ensure that extraction results in correct code, we 
  should ONLY interact with record _c types through this interface*)
Section ExtractInterface.

Definition node_of_ty (t: ty_c) : ty_node_c :=
  match t with
  | mk_ty_c n _ => n
  end.

Definition tag_of_ty (t: ty_c) : Weakhtbl.tag:=
  match t with
  | mk_ty_c _ n => n
  end.

Definition ident_of_tysym (t: tysymbol_c) : ident :=
  match t with
  | mk_ts_c t _ _ => t
  end.

Definition vars_of_tysym (t: tysymbol_c) : list tvsymbol :=
  match t with
  | mk_ts_c _ t _ => t
  end.

Definition type_def_of_tysym (t: tysymbol_c) : type_def ty_c :=
  match t with
  | mk_ts_c _ _ t => t
  end.

(*Finally, we need to extract a constructor, since
  the Record constructors are erased during extraction:*)

(*What we extract build_ts_c to:*)
Definition build_tysym_o (i: ident) (l: list tvsymbol) 
  (t: type_def ty_c) :
  tysymbol_o _ :=
  {| ts_name := i; ts_args := l;  ts_def := t |}.

Definition build_ty_o (n: ty_node_c) (i: Weakhtbl.tag) : ty_o _ :=
  {| ty_node := n; ty_tag := i |}.

End ExtractInterface.

(*Induction principle for types*)
Section TyInd.

Variable (P1: ty_c -> Prop).
Variable (P2: ty_node_c -> Prop).
Variable (P3: tysymbol_c -> Prop).

Variable (Hty: forall (t: ty_c),
  P2 (node_of_ty t) ->
  P1 t).

Variable (Hvar: forall (v: tvsymbol), P2 (Tyvar v)).
Variable (Happ: forall (ts: tysymbol_c) (tys: list ty_c),
  P3 ts -> Forall P1 tys -> P2 (Tyapp ts tys)).

Variable (Htysym: forall (t: tysymbol_c),
  match (type_def_of_tysym t) with
  | Alias a => P1 a
  | _ => True
  end -> P3 t).

Fixpoint ty_c_ind (t: ty_c) : P1 t :=
  Hty t (ty_node_c_ind (node_of_ty t))
with ty_node_c_ind (t: ty_node_c) : P2 t :=
  match t with
  | Tyvar v => Hvar v
  | Tyapp ts tys => Happ ts tys (tysymbol_c_ind ts)
    ((fix tys_ind (l: list ty_c) : Forall P1 l :=
      match l with
      | h :: t => Forall_cons _ h t (ty_c_ind h) (tys_ind t)
      | nil => Forall_nil _
      end) tys)
  end
with tysymbol_c_ind (t: tysymbol_c) : P3 t :=
  Htysym t (match type_def_of_tysym t as t' return
              (match t' with 
              | Alias a => P1 a
              | _ => True
              end) with
            | Alias a => ty_c_ind a
            | _ => I
  end).

Definition ty_mut_ind: 
  (forall (t: ty_c), P1 t) /\
  (forall (t: ty_node_c), P2 t) /\
  (forall (t: tysymbol_c), P3 t) :=
   conj (fun t => ty_c_ind t) 
  (conj (fun t => ty_node_c_ind t)
  (fun t => tysymbol_c_ind t)).

End TyInd.

(* Decidable Equality *)

Fixpoint ty_eqb (t1 t2: ty_c) : bool :=
  CoqBigInt.eqb (tag_of_ty t1) (tag_of_ty t2) &&
  ty_node_eqb (node_of_ty t1) (node_of_ty t2)
with ty_node_eqb (t1 t2: ty_node_c) : bool :=
  match t1, t2 with
  | Tyvar v1, Tyvar v2 => tvsymbol_eqb v1 v2
  | Tyapp ts1 tys1, Tyapp ts2 tys2 =>
    tysymbol_eqb ts1 ts2 &&
    (*TODO: not great - use OCaml length?*)
    Nat.eqb (length tys1) (length tys2) &&
    forallb id (map2 ty_eqb tys1 tys2)
  | _, _ => false
  end
with tysymbol_eqb (t1 t2: tysymbol_c) : bool :=
  ident_eqb (ident_of_tysym t1) (ident_of_tysym t2) &&
  list_eqb tvsymbol_eqb (vars_of_tysym t1) (vars_of_tysym t2) &&
  match type_def_of_tysym t1, type_def_of_tysym t2 with
  | NoDef, NoDef => true
  | Alias a1, Alias a2 => ty_eqb a1 a2
  | Range n1, Range n2 => Number.int_range_eqb n1 n2
  | Float f1, Float f2 => Number.float_format_eqb f1 f2
  | _, _ => false
  end.

Lemma ty_eqb_rewrite t1 t2:
  ty_eqb t1 t2 =
  match t1, t2 with
  | mk_ty_c n1 i1, mk_ty_c n2 i2 =>
    CoqBigInt.eqb i1 i2 && ty_node_eqb n1 n2
  end.
Proof.
  destruct t1; destruct t2; reflexivity.
Qed.

Lemma ty_eqb_eq_aux: 
  (forall t1 t2, t1 = t2 <-> ty_eqb t1 t2) /\
  (forall t1 t2, t1 = t2 <-> ty_node_eqb t1 t2) /\
  (forall t1 t2, t1 = t2 <-> tysymbol_eqb t1 t2).
Proof.
  apply ty_mut_ind.
  - intros t IH t2.
    rewrite ty_eqb_rewrite.
    destruct t as [n1 i1]; destruct t2 as [n2 i2]; simpl in *.
    rewrite andb_true, <- IH, <- CoqBigInt.eqb_eq.
    solve_eqb_eq.
  - intros. simpl. destruct t2 as [v2 |]; [| split; discriminate].
    rewrite <- tvsymbol_eqb_eq. solve_eqb_eq.
  - intros ts tys IHsym IHl.
    simpl.
    destruct t2 as [v2 | ts1 tys2]; [split;discriminate |].
    rewrite !andb_true, <- IHsym.
    destruct (Nat.eqb_spec (length tys) (length tys2)) as [Hlen| Hlen];
    [| solve_eqb_eq].
    (*TODO: maybe separate lemma*)
    assert (Hl: tys = tys2 <-> forallb id (map2 ty_eqb tys tys2)). {
      clear -IHl Hlen.
      generalize dependent tys2.
      induction tys as [| thd ttl IHtys]; simpl; intros [|th2 ttl2];
      try solve[split; solve[auto; discriminate]].
      simpl. intros Hlen.
      rewrite andb_true, <- (Forall_inv IHl th2), <- IHtys; auto.
      - solve_eqb_eq.
      - apply Forall_inv_tail in IHl; assumption.
    }
    rewrite <- Hl. solve_eqb_eq.
  - intros [i vs d]; simpl; intros IH [i1 vs2 d2]; simpl.
    rewrite !andb_true, <- ident_eqb_eq, <- (list_eqb_eq tvsymbol_eqb_eq).
    destruct d; destruct d2; simpl; try solve_eqb_eq.
    (*3 interesting cases*)
    + rewrite <- IH. solve_eqb_eq.
    + rewrite <- Number.int_range_eqb_eq. solve_eqb_eq.
    + rewrite <- Number.float_format_eqb_eq. solve_eqb_eq.
Qed. 

Definition ty_eqb_eq := proj1 ty_eqb_eq_aux.
Definition ty_node_eqb_eq := proj1 (proj2 ty_eqb_eq_aux).
Definition tysymbol_eqb_eq := proj2 (proj2 ty_eqb_eq_aux).

Definition tysymbol_eq : base.EqDecision tysymbol_c :=
  dec_from_eqb _ tysymbol_eqb_eq.


Module TsymTagged <: TaggedType.
Definition t := tysymbol_c.
Definition tag (ts: tysymbol_c) := (ident_of_tysym ts).(id_tag).
Definition eq := tysymbol_eq.
End TsymTagged.

Module Tsym := MakeMSH TsymTagged.
Module Sts := Tsym.S.
Module Mts := Tsym.M.
(*Module Hts := Tsym.H
  Module Wts := Tsym.W*)

Definition ts_equal (t1 t2: tysymbol_c) : bool := tysymbol_eqb t1 t2.
Definition ty_equal (t1 t2: ty_c) : bool := ty_eqb t1 t2.

Definition ts_hash (ts: tysymbol_c) := id_hash (ident_of_tysym ts).
Definition ty_hash (t: ty_c) := Weakhtbl.tag_hash (tag_of_ty t).
(*For now, skip ts_compare and ty_compare*)

(*Hash-consing equality is weaker*)
(*NOTE: in OCaml, ts_equal and ty_equal are reference equality
  because of hash consing - TODO: maybe change*)
Definition ty_equal_hash (ty1 ty2: ty_c) : bool :=
  match node_of_ty ty1, node_of_ty ty2 with
  | Tyvar n1, Tyvar n2 => tv_equal n1 n2
  | Tyapp s1 l1, Tyapp s2 l2 => 
    ts_equal s1 s2 && forallb id (map2 ty_equal l1 l2)
  | _, _ => false
  end.

Module TyHash <: Hashcons.HashedType.
Definition t := ty_c.
Definition equal (ty1 ty2: ty_c) : bool :=
  match node_of_ty ty1, node_of_ty ty2 with
  | Tyvar n1, Tyvar n2 => tv_equal n1 n2
  | Tyapp s1 l1, Tyapp s2 l2 => 
    ts_equal s1 s2 && forallb id (map2 ty_equal l1 l2)
  | _, _ => false
  end.
Definition hash (t: ty_c) : CoqBigInt.t :=
(*Note: in OCaml, we need to hash here bc we need an int,
  but ptree vs hash table makes it OK (though numbers are large!)*)
  match node_of_ty t with
    | Tyvar v => tv_hash v
    | Tyapp s tl => Hashcons.combine_big_list ty_hash (ts_hash s) tl
  end.

Definition tag n ty := mk_ty_c (node_of_ty ty) (Weakhtbl.create_tag n).
End TyHash.

Module Hsty := Hashcons.Make TyHash.

Definition mk_ts (name: preid) (args: list tvsymbol) (d: type_def ty_c) : 
  ctr tysymbol_c :=
  ctr_bnd (fun i => ctr_ret (mk_ts_c i args d)) (id_register name).

Definition ty_eq : base.EqDecision ty_c :=
  dec_from_eqb _ ty_eqb_eq.

Module TyTagged <: TaggedType.
Definition t := ty_c.
Definition tag (t: ty_c) := tag_of_ty t.
Definition eq := ty_eq.
End TyTagged.

Module TyM := MakeMSH TyTagged.
Module Sty := TyM.S.
Module Mty := TyM.M.
(*Module Hty := Ty.H
  Module Wty := Ty.W*)

Definition mk_ty (n: ty_node_c) : ty_c :=
  mk_ty_c n Weakhtbl.dummy_tag.

Definition ty_var (n: tvsymbol) : hashcons_st ty_c :=
  Hsty.hashcons (mk_ty (Tyvar n)).
Definition ty_app (s: tysymbol_c) (tl: list ty_c) : hashcons_st ty_c :=
  Hsty.hashcons (mk_ty (Tyapp s tl)).

(*Generic Traversal Functions*)
(*The reason we actually do want hash consing, or else
  the counter grows every time we call one of these functions*)
Definition ty_map (fn: ty_c -> ty_c) (t: ty_c) : hashcons_st ty_c :=
  match node_of_ty t with
  | Tyvar _ => hashcons_ret t
  | Tyapp f tl => ty_app f (map fn tl)
  end.

Definition ty_fold {A: Type} (fn: A -> ty_c -> A) (acc: A) (t: ty_c) : A :=
  match node_of_ty t with
  | Tyvar _ => acc
  | Tyapp _ tl => List.fold_left fn tl acc
  end.

Definition ty_all (pr: ty_c -> bool) (t: ty_c) : bool :=
  ty_fold (fun acc x => acc && (pr x)) true t.

Definition ty_any (pr: ty_c -> bool) (t: ty_c) : bool :=
  ty_fold (fun acc x => acc || (pr x)) false t.

Definition type_def_map {A: Type} (fn: A -> A) (x: type_def A) : type_def A :=
  match x with
  | Alias t => Alias (fn t)
  | _ => x
  end.