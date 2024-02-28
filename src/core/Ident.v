Require Export Coq.Strings.String.
Require Export Coq.Bool.Bool.
Require Export Coq.ZArith.ZArith.
Require Export CoqUtil.
Require Export Coq.Lists.List.
Export ListNotations.
(*From stdpp Require Export gmap.*)
Require Import Wstdlib.
Require Loc.

(*We include another prop-valued field (erased) during extraction
  asserting equality for 2 reasons:
  1. This prevents us from having to recompute the tag each time
  2. The OCaml type will be the same as the current API
  We use boolean equality for proof irrelevance*)
Record attribute := {
  attr_string : string;
  attr_tag : positive;
  attr_tag_eq: Pos.eqb attr_tag (str_to_pos attr_string)
}.

Definition attr_eqb (a1 a2: attribute) : bool :=
  String.eqb (attr_string a1) (attr_string a2).
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

Lemma attr_eqb_eq (a1 a2: attribute) : a1 = a2 <-> attr_eqb a1 a2 = true.
Proof.
  unfold attr_eqb.
  destruct a1 as [s1 p1 e1]; destruct a2 as [s2 p2 e2]; simpl.
  unfold is_true in e1, e2.
  destruct (String.eqb_spec s1 s2); subst; auto.
  2: {
    split;try discriminate;
    intro C; inversion C; subst; auto.
  }
  assert (p1 = p2). {
    rewrite Pos.eqb_eq in e1, e2; subst; reflexivity.
  }
  subst.
  assert (e1 = e2) by (apply bool_irrelevance); subst.
  split; reflexivity.
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

Definition create_attribute (s: string) : attribute :=
  Build_attribute s (str_to_pos s) (Pos.eqb_refl _).

(*NOTE: NO list_attributes because we don't store state*)

Definition attr_equal (a1 a2: attribute) : bool := attr_eqb a1 a2.
Definition attr_hash (a: attribute) : positive := a.(attr_tag).
Definition attr_compare (a1 a2: attribute) : comparison :=
  Pos.compare a1.(attr_tag) a2.(attr_tag).

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
  id_tag: positive;
  id_tag_eq: Pos.eqb id_tag (str_to_pos id_string)
}.

(*TODO: move*)
Definition option_eqb {A: Type} (eq: A -> A -> bool) (o1 o2: option A): bool :=
  match o1, o2 with
  | Some x, Some y => eq x y
  | None, None => true
  | _, _ => false
  end.

(*Decidable equality*)
Definition ident_eqb (i1 i2: ident) : bool :=
  String.eqb i1.(id_string) i2.(id_string) &&
  Sattr.equal i1.(id_attrs) i2.(id_attrs) &&
  option_eqb Loc.position_eqb i1.(id_loc) i2.(id_loc).

(*TODO: prove equality for Sets, options
  Need this to use as keys in sets and maps*)
Lemma ident_eqb_eq (i1 i2: ident): i1 = i2 <-> ident_eqb i1 i2.
Proof.
  unfold ident_eqb.
  revert i1 i2.
  intros [s1 a1 l1 p1 e1] [s2 a2 l2 p2 e2]; simpl.
  unfold is_true.
  rewrite !andb_true_iff, String.eqb_eq.


Module IdentTag <: TaggedType.
Definition t := ident.
Definition tag x := x.(id_tag).
Definition eq := 


Module AttrTag <: TaggedType.
Definition t := attribute.
Definition tag x := x.(attr_tag).
Definition eq := attr_eq.
End AttrTag.

Module Mid : Extmap.S.
Definition key := ident.
End Mid.

Definition list_attributes 



Definition tag : Set := positive.


(*
(*TODO: are modules right way to do this?*)
Module Type Ident.

Record attribute := {
  attr_string : string;
  attr_tag: positive
}.

Record ident := {
  id_string: string;
  id_attrs: gmap positive unit;
  id_loc: option position;
  id_tag: tag
}.

Parameter id_equal : ident -> ident -> bool.

End Ident.

Module IdentImpl <: Ident.*)

Record attribute := {
  attr_string : string;
  attr_tag: positive
}.

Record ident := {
  id_string: string;
  id_attrs: gmap positive unit;
  id_loc: option position;
  id_tag: tag
}.

(*Reference equality in OCaml impl*)
Definition id_equal (i1 i2: ident) : bool :=
  String.eqb (id_string i1) (id_string i2).
  (*TODO: more of course*)

(*End IdentImpl.*)

