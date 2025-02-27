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
Module AttrDecTag <: EqDecTag.
Definition t := attribute.
Definition tag x := x.(attr_tag).
Definition equal := attr_eqb.
Definition equal_eq := attr_eqb_eq.
End AttrDecTag.
Include MakeDecTag AttrDecTag.
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

Module IdentTag <: CoqWeakhtbl.Weakey.
  Definition t := ident.
  Definition tag x := x.(id_tag).
  Definition equal := ident_eqb_fast.
  Definition equal_eq := ident_eqb_eq.
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
Definition val := CoqBigInt.eighty.
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

(*1st 50 values of the counter correspond to builtin symbols
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

Definition id_derive1 nm (i : ident) :=
  create_ident nm (i.(id_attrs)) i.(id_loc).

(*Built in tuples*)
Definition id_tup0 : ident :=
  id_builtin "tuple0" (CoqWeakhtbl.create_tag (CoqBigInt.twelve)).

Definition id_tup1 : ident :=
  id_builtin "tuple1" (CoqWeakhtbl.create_tag (CoqBigInt.thirteen)).

Definition id_tup2 : ident :=
  id_builtin "tuple2" (CoqWeakhtbl.create_tag (CoqBigInt.fourteen)).

Definition id_tup3 : ident :=
  id_builtin "tuple3" (CoqWeakhtbl.create_tag (CoqBigInt.fifteen)).

Definition id_tup4 : ident :=
  id_builtin "tuple4" (CoqWeakhtbl.create_tag (CoqBigInt.sixteen)).

Definition id_tup5 : ident :=
  id_builtin "tuple5" (CoqWeakhtbl.create_tag (CoqBigInt.seventeen)).

Definition id_tup6 : ident :=
  id_builtin "tuple6" (CoqWeakhtbl.create_tag (CoqBigInt.eighteen)).

Definition id_tup7 : ident :=
  id_builtin "tuple7" (CoqWeakhtbl.create_tag (CoqBigInt.nineteen)).

Definition id_tup8 : ident :=
  id_builtin "tuple8" (CoqWeakhtbl.create_tag (CoqBigInt.twenty)).

Definition id_tup9 : ident :=
  id_builtin "tuple9" (CoqWeakhtbl.create_tag (CoqBigInt.twentyone)).

Definition id_tup10 : ident :=
  id_builtin "tuple10" (CoqWeakhtbl.create_tag (CoqBigInt.twentytwo)).

Definition id_tup11 : ident :=
  id_builtin "tuple11" (CoqWeakhtbl.create_tag (CoqBigInt.twentythree)).

Definition id_tup12 : ident :=
  id_builtin "tuple12" (CoqWeakhtbl.create_tag (CoqBigInt.twentyfour)).

Definition id_tup13 : ident :=
  id_builtin "tuple13" (CoqWeakhtbl.create_tag (CoqBigInt.twentyfive)).

Definition id_tup14 : ident :=
  id_builtin "tuple14" (CoqWeakhtbl.create_tag (CoqBigInt.twentysix)).

Definition id_tup15 : ident :=
  id_builtin "tuple15" (CoqWeakhtbl.create_tag (CoqBigInt.twentyseven)).

Definition id_tup16 : ident :=
  id_builtin "tuple16" (CoqWeakhtbl.create_tag (CoqBigInt.twentyeight)).

Definition id_tup17 : ident :=
  id_builtin "tuple17" (CoqWeakhtbl.create_tag (CoqBigInt.twentynine)).

Definition id_tup18 : ident :=
  id_builtin "tuple18" (CoqWeakhtbl.create_tag (CoqBigInt.thirty)).

Definition id_tup19 : ident :=
  id_builtin "tuple19" (CoqWeakhtbl.create_tag (CoqBigInt.thirtyone)).

Definition id_tup20 : ident :=
  id_builtin "tuple20" (CoqWeakhtbl.create_tag (CoqBigInt.thirtytwo)).

Definition id_tup_list : list ident :=
  [id_tup0; id_tup1; id_tup2; id_tup3; id_tup4; id_tup5; id_tup6; id_tup7; id_tup8; id_tup9; id_tup10; 
   id_tup11; id_tup12; id_tup13; id_tup14; id_tup15; id_tup16;
   id_tup17; id_tup18; id_tup19; id_tup20].

(*And more typesymbols*)
Definition id_c : ident :=
  id_builtin "c" (CoqWeakhtbl.create_tag CoqBigInt.thirtythree).

Definition id_d : ident :=
  id_builtin "d" (CoqWeakhtbl.create_tag CoqBigInt.thirtyfour).

Definition id_e : ident :=
  id_builtin "e" (CoqWeakhtbl.create_tag CoqBigInt.thirtyfive).

Definition id_f : ident :=
  id_builtin "f" (CoqWeakhtbl.create_tag CoqBigInt.thirtysix).

Definition id_g : ident :=
  id_builtin "g" (CoqWeakhtbl.create_tag CoqBigInt.thirtyseven).

Definition id_h : ident :=
  id_builtin "h" (CoqWeakhtbl.create_tag CoqBigInt.thirtyeight).

Definition id_i : ident :=
  id_builtin "i" (CoqWeakhtbl.create_tag CoqBigInt.thirtynine).

Definition id_j : ident :=
  id_builtin "j" (CoqWeakhtbl.create_tag CoqBigInt.forty).

Definition id_k : ident :=
  id_builtin "k" (CoqWeakhtbl.create_tag CoqBigInt.fortyone).

Definition id_l : ident :=
  id_builtin "l" (CoqWeakhtbl.create_tag CoqBigInt.fortytwo).

Definition id_m : ident :=
  id_builtin "m" (CoqWeakhtbl.create_tag CoqBigInt.fortythree).

Definition id_n : ident :=
  id_builtin "n" (CoqWeakhtbl.create_tag CoqBigInt.fortyfour).

Definition id_o : ident :=
  id_builtin "o" (CoqWeakhtbl.create_tag CoqBigInt.fortyfive).

Definition id_p : ident :=
  id_builtin "p" (CoqWeakhtbl.create_tag CoqBigInt.fortysix).

Definition id_q : ident :=
  id_builtin "q" (CoqWeakhtbl.create_tag CoqBigInt.fortyseven).

Definition id_r : ident :=
  id_builtin "r" (CoqWeakhtbl.create_tag CoqBigInt.fortyeight).

Definition id_s : ident :=
  id_builtin "s" (CoqWeakhtbl.create_tag CoqBigInt.fortynine).

Definition id_t : ident :=
  id_builtin "t" (CoqWeakhtbl.create_tag CoqBigInt.fifty).

(*The next 10 just have numbers*)
Definition id_a1 : ident :=
  id_builtin "a1" (CoqWeakhtbl.create_tag CoqBigInt.fiftyone).
Definition id_a2 : ident :=
  id_builtin "a2" (CoqWeakhtbl.create_tag CoqBigInt.fiftytwo).
Definition id_a3 : ident :=
  id_builtin "a3" (CoqWeakhtbl.create_tag CoqBigInt.fiftythree).
Definition id_a4 : ident :=
  id_builtin "a4" (CoqWeakhtbl.create_tag CoqBigInt.fiftyfour).
Definition id_a5 : ident :=
  id_builtin "a5" (CoqWeakhtbl.create_tag CoqBigInt.fiftyfive).
Definition id_a6 : ident :=
  id_builtin "a6" (CoqWeakhtbl.create_tag CoqBigInt.fiftysix).
Definition id_a7 : ident :=
  id_builtin "a7" (CoqWeakhtbl.create_tag CoqBigInt.fiftyseven).
Definition id_a8 : ident :=
  id_builtin "a8" (CoqWeakhtbl.create_tag CoqBigInt.fiftyeight).
Definition id_a9 : ident :=
  id_builtin "a9" (CoqWeakhtbl.create_tag CoqBigInt.fiftynine).
Definition id_b0 : ident :=
  id_builtin "b0" (CoqWeakhtbl.create_tag CoqBigInt.sixty).
Definition id_b1 : ident :=
  id_builtin "b1" (CoqWeakhtbl.create_tag CoqBigInt.sixtyone).
Definition id_b2 : ident :=
  id_builtin "b2" (CoqWeakhtbl.create_tag CoqBigInt.sixtytwo).
Definition id_b3 : ident :=
  id_builtin "b3" (CoqWeakhtbl.create_tag CoqBigInt.sixtythree).
Definition id_b4 : ident :=
  id_builtin "b4" (CoqWeakhtbl.create_tag CoqBigInt.sixtyfour).
Definition id_b5 : ident :=
  id_builtin "b5" (CoqWeakhtbl.create_tag CoqBigInt.sixtyfive).
Definition id_b6 : ident :=
  id_builtin "b6" (CoqWeakhtbl.create_tag CoqBigInt.sixtysix).

Definition id_tup21 : ident :=
  id_builtin "tuple21" (CoqWeakhtbl.create_tag (CoqBigInt.sixtyseven)).
Definition id_tup22 : ident :=
  id_builtin "tuple22" (CoqWeakhtbl.create_tag (CoqBigInt.sixtyeight)).
Definition id_tup23 : ident :=
  id_builtin "tuple23" (CoqWeakhtbl.create_tag (CoqBigInt.sixtynine)).
Definition id_tup24 : ident :=
  id_builtin "tuple24" (CoqWeakhtbl.create_tag (CoqBigInt.seventy)).
Definition id_tup25 : ident :=
  id_builtin "tuple25" (CoqWeakhtbl.create_tag (CoqBigInt.seventyone)).
Definition id_tup26 : ident :=
  id_builtin "tuple26" (CoqWeakhtbl.create_tag (CoqBigInt.seventytwo)).
Definition id_tup27 : ident :=
  id_builtin "tuple27" (CoqWeakhtbl.create_tag (CoqBigInt.seventythree)).
Definition id_tup28 : ident :=
  id_builtin "tuple28" (CoqWeakhtbl.create_tag (CoqBigInt.seventyfour)).
Definition id_tup29 : ident :=
  id_builtin "tuple29" (CoqWeakhtbl.create_tag (CoqBigInt.seventyfive)).
Definition id_tup30 : ident :=
  id_builtin "tuple30" (CoqWeakhtbl.create_tag (CoqBigInt.seventysix)).
Definition id_tup31 : ident :=
  id_builtin "tuple31" (CoqWeakhtbl.create_tag (CoqBigInt.seventyseven)).
Definition id_tup33 : ident :=
  id_builtin "tuple33" (CoqWeakhtbl.create_tag (CoqBigInt.seventyeight)).
Definition id_tup36 : ident :=
  id_builtin "tuple36" (CoqWeakhtbl.create_tag (CoqBigInt.seventynine)).