Require Export Coq.Strings.String.
Require Export Coq.Bool.Bool.
Require Export Coq.ZArith.ZArith.
Require Export CoqUtil.
Require Export Coq.Lists.List.
Require CoqBigInt.
Export ListNotations.
(*From stdpp Require Export gmap.*)
Require Import CoqWstdlib.
Require LocTy.
Require Export Monads.
Require Import CoqCtr.
Import MonadNotations.
Local Open Scope state_scope.
Set Bullet Behavior "Strict Subproofs".

(*We include another prop-valued field (erased) during extraction
  asserting equality for 2 reasons:
  1. This prevents us from having to recompute the tag each time
  2. The OCaml type will be the same as the current API
  We use boolean equality for proof irrelevance*)
Record attribute := {
  attr_string : string;
  attr_tag : CoqBigInt.t;
  (*attr_tag_eq: Pos.eqb attr_tag (str_to_pos attr_string)*)
}.

Definition attr_eqb (a1 a2: attribute) : bool :=
  String.eqb (attr_string a1) (attr_string a2) &&
  CoqBigInt.eqb (attr_tag a1) (attr_tag a2).
  (*Pos.eqb (attr_tag a1) (attr_tag a2).*)

Lemma attr_eqb_eq (a1 a2: attribute) : a1 = a2 <-> attr_eqb a1 a2.
Proof.
  unfold attr_eqb.
  destruct a1 as [s1 p1]; destruct a2 as [s2 p2]; simpl.
  rewrite andb_true, <- CoqBigInt.eqb_eq.
  unfold is_true. rewrite String.eqb_eq.
  solve_eqb_eq.
Qed.

Module AttrTag <: TaggedType.
Definition t := attribute.
Definition tag x := x.(attr_tag).
Definition equal := attr_eqb.
End AttrTag.

Module Attr  := MakeMS AttrTag.
Module Sattr := Attr.S.
Module Mattr := Attr.M.

(*NOTE: no Hashcons
  also, don't understand purpose of tag: items are hashed by string,
  so why would we ever need same attribute with same name but different
  tag?*)

(*NOTE: in Why3, have -1 (TODO: make sure this is OK)*)
(*TODO: see if we need
Definition create_attribute (s: string) : attribute :=
  Build_attribute s (CoqBigInt.zero).*)

(*NOTE: NO list_attributes because we don't store state*)

Definition attr_equal (a1 a2: attribute) : bool := attr_eqb a1 a2.
Definition attr_hash (a: attribute) : CoqBigInt.t := a.(attr_tag).
Definition attr_compare (a1 a2: attribute) : int :=
  CoqBigInt.compare a1.(attr_tag) a2.(attr_tag).

(*NOTE: anything we don't need we will put in a separate OCaml file*)

(*TODO: do we need this?*)
Variant notation :=
  | SNword : string -> notation (* plus *)
  | SNinfix : string -> notation (* + *)
  | SNtight : string -> notation (* ! *)
  | SNprefix : string -> notation (* -_ *)
  | SNget : string -> notation (* [] *)
  | SNset : string -> notation (* []<- *)
  | SNupdate : string -> notation (* [<-] *)
  | SNcut : string -> notation (* [..] *)
  | SNlcut : string -> notation (* [.._] *)
  | SNrcut : string -> notation (* [_..] *).

(*Current encodings*)
Section Encode.
Local Open Scope string_scope.

Definition op_infix s := "infix " ++ s.
Definition op_prefix s := "prefix " ++ s.
Definition op_get s := "mixfix []" ++ s.
Definition op_set s := "mixfix []<-" ++ s.
Definition op_update s := "mixfix [<-]" ++ s.
Definition op_cut s := "mixfix [..]" ++ s.
Definition op_lcut s := "mixfix [.._]" ++ s.
Definition op_rcut s := "mixfix [_..]" ++ s.

Definition op_equ := op_infix "=".
Definition op_neq := op_infix "<>".
Definition op_tight := op_prefix.

End Encode.

(*Skipped [print_sn], [sn_decode], [print_decoded]*)

(** Identifiers **)
Record ident := {
  id_string : string;
  id_attrs: Sattr.t;
  id_loc: option LocTy.position;
  id_tag: CoqWeakhtbl.tag; (*TODO: weakhtbl i think*)
}.

(*Decidable equality*)
Definition ident_eqb (i1 i2: ident) : bool :=
  (*tag first for fast eq*)
  CoqWeakhtbl.tag_equal i1.(id_tag) i2.(id_tag) &&
  String.eqb i1.(id_string) i2.(id_string) &&
  Sattr.equal i1.(id_attrs) i2.(id_attrs) &&
  option_eqb LocTy.equal i1.(id_loc) i2.(id_loc).

Definition ident_eqb_fast := ident_eqb.

(*TODO: prove equality for Sets, options
  Need this to use as keys in sets and maps*)
Lemma ident_eqb_eq (i1 i2: ident): i1 = i2 <-> ident_eqb i1 i2.
Proof.
  unfold ident_eqb.
  revert i1 i2.
  intros [s1 a1 l1 p1] [s2 a2 l2 p2]; simpl.
  rewrite !andb_true, <- (option_eqb_eq LocTy.position_eqb_eq),
    <- CoqBigInt.eqb_eq, <- (Sattr.equal_eq attr_eqb_eq).
  unfold is_true.
  rewrite String.eqb_eq.
  solve_eqb_eq.
Qed.

Module IdentTag <: TaggedType.
Definition t := ident.
Definition tag x := x.(id_tag).
Definition equal := ident_eqb_fast.

End IdentTag.

(*NOTE: we do not have weak hash tables, so we ignore the W.
  This seems to be used for sharing and optimizations, we may
  need to add something similar later (maybe with PTrees)*)
Module Id := CoqWstdlib.MakeMSWeak IdentTag.
Module Sid := Id.S.
Module Mid := Id.M.
(*module Hid = Id.H
module Wid = Id.W*)

Record preid := {
  pre_name : string;
  pre_attrs : Sattr.t;
  pre_loc : option LocTy.position
}.

(*In OCaml, this is reference equality (==).*)
Definition id_equal (i1 i2: ident) : bool := ident_eqb_fast i1 i2.
Definition id_hash (i: ident) : CoqBigInt.t := CoqWeakhtbl.tag_hash (i.(id_tag)).
Definition id_compare (id1 id2: ident) : CoqInt.int :=
  CoqBigInt.compare (id_hash id1) (id_hash id2).

Module CtrStart <: BigIntVal.
Definition val := CoqBigInt.thirteen.
End CtrStart. 
Module IdCtr := MakeCtr(CtrStart).
(*TODO: we need to ensure that this is called in Coq - need
  some sort of wrapper I think*)
Definition id_ctr : ctr unit := IdCtr.create.

(*Constructors*)

Definition id_register : preid -> ctr ident :=
  fun p =>
    _ <- IdCtr.incr tt ;;
    i <- IdCtr.get tt ;;
    st_ret {| id_string := p.(pre_name);
    id_attrs := p.(pre_attrs);
    id_loc := p.(pre_loc);
    id_tag := CoqWeakhtbl.create_tag i |}.

(*1st 10 values of the counter correspond to builtin symbols
  (so that we don't need state)*)
Definition id_builtin (name: string) (tag: CoqBigInt.t) : ident :=
  {| id_string := name;
     id_attrs := Sattr.empty;
     id_loc := None;
     id_tag := tag |}.
  
Definition id_int : ident :=
  id_builtin "int" (CoqWeakhtbl.create_tag CoqBigInt.one).

Definition id_real : ident :=
  id_builtin "real" (CoqWeakhtbl.create_tag CoqBigInt.two).

Definition id_bool : ident :=
  id_builtin "bool" (CoqWeakhtbl.create_tag CoqBigInt.three).

Definition id_str : ident :=
  id_builtin "string" (CoqWeakhtbl.create_tag CoqBigInt.four).

(*JOSH: TODO: can this be the same for function and equ
  types?*)
Definition id_a : ident :=
  id_builtin "a" (CoqWeakhtbl.create_tag CoqBigInt.five).

Definition id_b : ident :=
  id_builtin "b" (CoqWeakhtbl.create_tag CoqBigInt.six).

Definition id_fun : ident :=
  id_builtin (op_infix "->") (CoqWeakhtbl.create_tag CoqBigInt.seven).

Definition id_eq : ident :=
  id_builtin (op_infix "=") (CoqWeakhtbl.create_tag CoqBigInt.eight). 

Definition id_true : ident :=
  id_builtin "True" (CoqWeakhtbl.create_tag CoqBigInt.nine).

Definition id_false : ident :=
  id_builtin "False" (CoqWeakhtbl.create_tag CoqBigInt.ten).

Definition id_app : ident :=
  id_builtin (op_infix "@") (CoqWeakhtbl.create_tag CoqBigInt.eleven).

Definition create_ident name attrs loc :=
  {| pre_name := name; pre_attrs := attrs; pre_loc := loc|}.

(*NOTE: different signature than OCaml, which uses optional args*)
(*For that reason, we give it a different name*)
Definition id_fresh1 (s: string) : preid :=
  create_ident s Sattr.empty None.

Definition id_clone1 loc attrs i :=
  let aa := Sattr.union attrs i.(id_attrs) in
  let loc := match loc with
            | None => i.(id_loc)
            | Some _ => loc
  end in
  create_ident i.(id_string) aa loc.