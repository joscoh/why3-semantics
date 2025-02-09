Require Import CoqWstdlib.
Require Export IdentDefs.
Require NumberDefs.
Require hashcons CoqWeakhtbl CoqHashtbl. 
(* Require Import stdpp.base. *)
Require Import Coq.Wellfounded.Inverse_Image.
Require Import IntFuncs.
Require Import CoqExthtbl.
Import MonadNotations.
Local Open Scope state_scope.
Set Bullet Behavior "Strict Subproofs".

Record tvsymbol := {
  tv_name : ident
}.

Definition tvsymbol_eqb (t1 t2: tvsymbol) : bool :=
  id_equal t1.(tv_name) t2.(tv_name).

Lemma tvsymbol_eqb_eq (t1 t2: tvsymbol): t1 = t2 <-> 
  tvsymbol_eqb t1 t2.
Proof.
  unfold tvsymbol_eqb.
  rewrite <- ident_eqb_eq.
  destruct t1 as [t1]; destruct t2 as [t2]; simpl; solve_eqb_eq. 
Qed.

Module TvarTagged <: CoqWeakhtbl.Weakey.
Definition t := tvsymbol.
Definition tag tv := tv.(tv_name).(id_tag).
Definition equal := tvsymbol_eqb.
Definition equal_eq := tvsymbol_eqb_eq.
End TvarTagged.

Module Tvar := MakeMSWeak TvarTagged.
Module Stv := Tvar.S.
Module Mtv := Tvar.M.
(*Module Htv := Tvar.H*)

(*== in OCaml*)
Definition tv_equal (t1 t2: tvsymbol) : bool := tvsymbol_eqb t1 t2.
Definition tv_hash tv := id_hash tv.(tv_name).
Definition tv_compare (tv1 tv2: tvsymbol) : CoqInt.int :=
  id_compare tv1.(tv_name) tv2.(tv_name).

Definition create_tvsymbol (n: preid) : ctr tvsymbol :=
  i <- id_register n ;;
  st_ret {|tv_name := i|}.

(*Note: ONLY for builtins*)
Definition create_tvsymbol_builtin (i: ident) : tvsymbol :=
  {| tv_name := i|}.

(*This has to be a stateful function which finds the existing
  identifier for the string if it has been created.
  Other parts of the OCaml Why3 code rely on the 
  same string giving the same result (ironically, we need
  state to make this a pure function)*)
(*TODO: monad transformer prob*)
Module Tvsym_t <: CoqExthtbl.ModTySimpl.
Definition t := tvsymbol.
End Tvsym_t.
Module Hstr_tv := CoqExthtbl.MakeExthtbl(CoqWstdlib.Str2)(Tvsym_t).

(*TODO: need to use in Coq*)
Definition tv_hashtbl : hash_st string tvsymbol unit 
  := @Hstr_tv.create CoqInt.one.

Definition tv_of_string (s: string) : st (CoqBigInt.t * CoqHashtbl.hashtbl string tvsymbol) tvsymbol :=
  o <- (st_lift2 (Hstr_tv.find_opt s)) ;;
  match o with
    | None => 
      let tv := create_tvsymbol (id_fresh1 s) in
      i <- (st_lift1 tv) ;;
      _ <- (st_lift2 (Hstr_tv.add s i)) ;;
      st_ret i
    | Some v => st_ret v
  end.

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
  | Range: NumberDefs.int_range -> type_def A
  | Float: NumberDefs.float_format -> type_def A.

Arguments NoDef {_}.
Arguments Alias {_}.
Arguments Range {_}.
Arguments Float {_}.

Record ty_o (A: Type) := 
  mk_ty_o { ty_node: A;
    ty_tag: CoqWeakhtbl.tag}.
    
Record tysymbol_o (A: Type) := mk_ts_o {
  ts_name : ident;
  ts_args : list tvsymbol;
  ts_def : type_def A
}.

(*Coq types - we append with _c for coq*)
Inductive ty_c : Type :=
  | mk_ty_c : ty_node_c -> CoqWeakhtbl.tag -> ty_c
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

Definition ty_node_of (t: ty_c) : ty_node_c :=
  match t with
  | mk_ty_c n _ => n
  end.

Definition ty_tag_of (t: ty_c) : CoqWeakhtbl.tag:=
  match t with
  | mk_ty_c _ n => n
  end.

Definition ts_name_of (t: tysymbol_c) : ident :=
  match t with
  | mk_ts_c t _ _ => t
  end.

Definition ts_args_of (t: tysymbol_c) : list tvsymbol :=
  match t with
  | mk_ts_c _ t _ => t
  end.

Definition ts_def_of (t: tysymbol_c) : type_def ty_c :=
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

Definition build_ty_o (n: ty_node_c) (i: CoqWeakhtbl.tag) : ty_o _ :=
  {| ty_node := n; ty_tag := i |}.

End ExtractInterface.

(*Induction principle for types*)
Section TyInd.

Variable (P1: ty_c -> Prop).
Variable (P2: ty_node_c -> Prop).
Variable (P3: tysymbol_c -> Prop).

Variable (Hty: forall (t: ty_c),
  P2 (ty_node_of t) ->
  P1 t).

Variable (Hvar: forall (v: tvsymbol), P2 (Tyvar v)).
Variable (Happ: forall (ts: tysymbol_c) (tys: list ty_c),
  P3 ts -> Forall P1 tys -> P2 (Tyapp ts tys)).

Variable (Htysym: forall (t: tysymbol_c),
  match (ts_def_of t) with
  | Alias a => P1 a
  | _ => True
  end -> P3 t).

Fixpoint ty_c_ind (t: ty_c) : P1 t :=
  Hty t (ty_node_c_ind (ty_node_of t))
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
  Htysym t (match ts_def_of t as t' return
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
  CoqWeakhtbl.tag_equal (ty_tag_of t1) (ty_tag_of t2) &&
  ty_node_eqb (ty_node_of t1) (ty_node_of t2)
with ty_node_eqb (t1 t2: ty_node_c) : bool :=
  match t1, t2 with
  | Tyvar v1, Tyvar v2 => tvsymbol_eqb v1 v2
  | Tyapp ts1 tys1, Tyapp ts2 tys2 =>
    tysymbol_eqb ts1 ts2 &&
    (*TODO: not great - use OCaml length?*)
    CoqBigInt.eqb (int_length tys1) (int_length tys2) &&
    (*Nat.eqb (length tys1) (length tys2) &&*)
    forallb (fun x => x) (map2 ty_eqb tys1 tys2)
  | _, _ => false
  end
with tysymbol_eqb (t1 t2: tysymbol_c) : bool :=
  id_equal (ts_name_of t1) (ts_name_of t2) &&
  list_eqb tvsymbol_eqb (ts_args_of t1) (ts_args_of t2) &&
  match ts_def_of t1, ts_def_of t2 with
  | NoDef, NoDef => true
  | Alias a1, Alias a2 => ty_eqb a1 a2
  | Range n1, Range n2 => NumberDefs.int_range_eqb n1 n2
  | Float f1, Float f2 => NumberDefs.float_format_eqb f1 f2
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

Lemma destruct_bool (b: bool) :
  b \/ ~ b.
Proof.
  destruct b; [left | right]; auto; discriminate.
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
    rewrite !andb_true, <- IHsym, int_length_eq, <- nat_eqb_eq.
    rewrite and_assoc, <- (forall_eqb_eq IHl).
    solve_eqb_eq.
  - intros [i vs d]; simpl; intros IH [i1 vs2 d2]; simpl.
    rewrite !andb_true, <- ident_eqb_eq, <- (list_eqb_eq tvsymbol_eqb_eq).
    destruct d; destruct d2; simpl; try solve_eqb_eq.
    (*3 interesting cases*)
    + rewrite <- IH. solve_eqb_eq.
    + rewrite <- NumberDefs.int_range_eqb_eq. solve_eqb_eq.
    + rewrite <- NumberDefs.float_format_eqb_eq. solve_eqb_eq.
Qed. 

Definition ty_eqb_eq := proj1 ty_eqb_eq_aux.
Definition ty_node_eqb_eq := proj1 (proj2 ty_eqb_eq_aux).
Definition tysymbol_eqb_eq := proj2 (proj2 ty_eqb_eq_aux).

Definition ty_eqb_fast := ty_eqb.
Definition tysymbol_eqb_fast := tysymbol_eqb.

Module TsymTagged <: CoqWeakhtbl.Weakey.
Definition t := tysymbol_c.
Definition tag (ts: tysymbol_c) := (ts_name_of ts).(id_tag).
Definition equal := tysymbol_eqb_fast.
Definition equal_eq := tysymbol_eqb_eq.
End TsymTagged.

Module Tsym := MakeMSWeak TsymTagged.
Module Sts := Tsym.S.
Module Mts := Tsym.M.
(*Module Hts := Tsym.H
  Module Wts := Tsym.W*)

Definition ts_equal (t1 t2: tysymbol_c) : bool := tysymbol_eqb_fast t1 t2.
Definition ty_equal (t1 t2: ty_c) : bool := ty_eqb_fast t1 t2.

Definition ts_hash (ts: tysymbol_c) := id_hash (ts_name_of ts).
Definition ty_hash (t: ty_c) := CoqWeakhtbl.tag_hash (ty_tag_of t).
Definition ts_compare (ts1 ts2: tysymbol_c) : int :=
  id_compare (ts_name_of ts1) (ts_name_of ts2).
Definition ty_compare (ty1 ty2: ty_c) : int :=
  CoqBigInt.compare (ty_hash ty1) (ty_hash ty2).

(*Hash-consing equality is weaker*)

Module TyHash <: hashcons.HashedType.
Definition t := ty_c.
Definition equal (ty1 ty2: ty_c) : bool :=
  match ty_node_of ty1, ty_node_of ty2 with
  | Tyvar n1, Tyvar n2 => tv_equal n1 n2
  | Tyapp s1 l1, Tyapp s2 l2 => 
    tysymbol_eqb_fast s1 s2 && forallb (fun x => x) (map2 ty_eqb_fast l1 l2)
  | _, _ => false
  end.
Definition hash (t: ty_c) : CoqBigInt.t :=
(*Note: in OCaml, we need to hash here bc we need an int,
  but ptree vs hash table makes it OK (though numbers are large!)*)
  match ty_node_of t with
    | Tyvar v => tv_hash v
    | Tyapp s tl => hashcons.combine_big_list ty_hash (ts_hash s) tl
  end.

Definition tag n ty := mk_ty_c (ty_node_of ty) (CoqWeakhtbl.create_tag n).
End TyHash.

Module Hsty := hashcons.Make TyHash.

Definition mk_ts (name: preid) (args: list tvsymbol) (d: type_def ty_c) : 
  ctr tysymbol_c :=
  i <- id_register name ;;
  st_ret (mk_ts_c i args d).

Module TyTagged <: CoqWeakhtbl.Weakey.
Definition t := ty_c.
Definition tag (t: ty_c) := ty_tag_of t.
Definition equal := ty_eqb_fast.
Definition equal_eq := ty_eqb_eq.
End TyTagged.

Module TyM := MakeMSWeak TyTagged.
Module Sty := TyM.S.
Module Mty := TyM.M.