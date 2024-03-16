Require Export Coq.Strings.String.
Require Export Coq.Bool.Bool.
Require Export Coq.ZArith.ZArith.
Require Export CoqUtil.
Require Export Coq.Lists.List.
Require CoqBigInt.
Export ListNotations.
(*From stdpp Require Export gmap.*)
Require Import Wstdlib.
Require Loc.
Require Export StateMonad.

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

(*NOTE: don't use reflect because we want all proofs to be
  erased*)
Definition dec_from_eqb {A: Type} (f: A -> A -> bool) 
  (H: forall (x y: A), x = y <-> f x y = true) :
  forall (x y: A), {x = y} + {x <> y}.
Proof.
  intros x y.
  specialize (H x y).
  destruct (f x y).
  - left. apply H. reflexivity.
  - right. intro C. apply H in C. discriminate.
Defined.

Lemma attr_eqb_eq (a1 a2: attribute) : a1 = a2 <-> attr_eqb a1 a2.
Proof.
  unfold attr_eqb.
  destruct a1 as [s1 p1]; destruct a2 as [s2 p2]; simpl.
  rewrite andb_true, <- CoqBigInt.eqb_eq.
  unfold is_true. rewrite String.eqb_eq.
  solve_eqb_eq.
Qed.

Definition attr_eq : base.EqDecision attribute :=
  dec_from_eqb attr_eqb attr_eqb_eq.

Module AttrTag <: TaggedType.
Definition t := attribute.
Definition tag x := x.(attr_tag).
Definition eq := attr_eq.
End AttrTag.

Module Attr  := MakeMSH AttrTag.
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
  id_loc: option Loc.position;
  id_tag: CoqBigInt.t; (*TODO: weakhtbl i think*)
}.

(*Decidable equality*)
Definition ident_eqb (i1 i2: ident) : bool :=
  String.eqb i1.(id_string) i2.(id_string) &&
  Sattr.equal i1.(id_attrs) i2.(id_attrs) &&
  option_eqb Loc.position_eqb i1.(id_loc) i2.(id_loc) &&
  CoqBigInt.eqb i1.(id_tag) i2.(id_tag).

(*TODO: prove equality for Sets, options
  Need this to use as keys in sets and maps*)
Lemma ident_eqb_eq (i1 i2: ident): i1 = i2 <-> ident_eqb i1 i2.
Proof.
  unfold ident_eqb.
  revert i1 i2.
  intros [s1 a1 l1 p1] [s2 a2 l2 p2]; simpl.
  rewrite !andb_true, <- (option_eqb_eq Loc.position_eqb_eq),
    <- CoqBigInt.eqb_eq.
  unfold is_true.
  rewrite String.eqb_eq,  <- Sattr.equal_eq.
  solve_eqb_eq.
Qed.

Definition ident_eq : base.EqDecision ident :=
  dec_from_eqb ident_eqb ident_eqb_eq.

Module IdentTag <: TaggedType.
Definition t := ident.
Definition tag x := x.(id_tag).
Definition eq := ident_eq.

End IdentTag.

(*NOTE: we do not have weak hash tables, so we ignore the W.
  This seems to be used for sharing and optimizations, we may
  need to add something similar later (maybe with PTrees)*)
Module Id := Wstdlib.MakeMSH IdentTag.
Module Sid := Id.S.
Module Mid := Id.M.
(*module Hid = Id.H
module Wid = Id.W*)

Record preid := {
  pre_name : string;
  pre_attrs : Sattr.t;
  pre_loc : option Loc.position
}.

(*In OCaml, this is reference equality (==).
  TODO: we could axiomatize and assume x == y -> x = y
  (and nothing about false). But for now, OK to do
  structural equality I think*)
Definition id_equal (i1 i2: ident) : bool := ident_eqb i1 i2.
Definition id_hash (i: ident) : CoqBigInt.t := i.(id_tag).
(*Skip id_compare*) 

Require Import stdpp.base.
(*Constructors*)
(*NOTE: for us, registering just calculates the tag
  instead of changing state. We need to see if this is
  a problem.
  If the same id string is used multiple times, they
  will have the same tag*)
Definition id_ctr : ctr_unit :=
  new_ctr. (*For extraction*)

Definition id_register : preid -> ctr ident :=
  fun p =>
  ctr_bnd (fun _ => ctr_bnd (fun i => ctr_ret 
    {| id_string := p.(pre_name);
    id_attrs := p.(pre_attrs);
    id_loc := p.(pre_loc);
    id_tag := i |}) ctr_get) incr.

(*1st 7 values of the counter correspond to builtin symbols
  (so that we don't need state)*)
Definition id_builtin (name: string) (tag: CoqBigInt.t) : ident :=
  {| id_string := name;
     id_attrs := Sattr.empty;
     id_loc := None;
     id_tag := tag |}.
  
Definition id_int : ident :=
  id_builtin "int" CoqBigInt.one.

Definition id_real : ident :=
  id_builtin "real" CoqBigInt.two.

Definition id_bool : ident :=
  id_builtin "bool" CoqBigInt.three.

Definition id_str : ident :=
  id_builtin "string" CoqBigInt.four.

Definition id_a : ident :=
  id_builtin "a" CoqBigInt.five.

Definition id_b : ident :=
  id_builtin "b" CoqBigInt.six.

Definition id_fun : ident :=
  id_builtin (op_infix "->") CoqBigInt.seven.

Definition create_ident name attrs loc :=
  {| pre_name := name; pre_attrs := attrs; pre_loc := loc|}.

(*NOTE: different signature than OCaml, which uses optional args*)
Definition id_fresh (s: string) : preid :=
  create_ident s Sattr.empty None.
