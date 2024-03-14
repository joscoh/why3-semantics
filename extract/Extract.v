From Src.core Require Import Ident Ty.
From Src.util Require Import Extmap Extset.
From stdpp Require Import gmap.
From Coq Require Extraction.

Extraction Blacklist String List.

Require Import Coq.extraction.ExtrOcamlBasic.
(*Extract to native OCaml strings*)
Require Import Coq.extraction.ExtrOcamlNativeString.

Set Extraction KeepSingleton.

(*Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive prod => "(*)"  [ "(,)" ].*)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

Extract Inlined Constant proj_sumbool => "".

(*Axiomatize OCaml ints and BigInts*)
(*TODO: move to approprate files?*)
(*TODO: We need this module stuff for now because dune does not
  support (include_subdirs unqualified) with Coq*)
Extract Inlined Constant CoqBigInt.t => "Why3OCaml.BigInt.t".
Extract Inlined Constant CoqBigInt.zero => "Why3OCaml.BigInt.zero" (*TODO: change to BigInt when put in Why3*).
Extract Inlined Constant CoqBigInt.one => "BigInt.one" (*TODO*).
Extract Inlined Constant CoqBigInt.succ => "Why3OCaml.BigInt.succ".
Extract Inlined Constant CoqBigInt.eqb => "Why3OCaml.BigInt.eq".

Extract Inlined Constant CoqInt.int => "Int.t".
Extract Inlined Constant CoqInt.int_eqb => "Int.equal".

(*TODO: this is BAD - figure out better*)
Extract Inlined Constant length => "List.length".
Extract Inlined Constant Coq.Arith.PeanoNat.Nat.eqb => "Int.equal".

(*Handle exception monad*)

Extract Inductive errorM => "  " ["Normal" "Error"] .  
Extract Inductive errtype => exn ["Not_found" "Invalid_argument"].
Extract Inlined Constant ret => "".
Extract Inlined Constant throw => " raise ".
(*TODO: see*)
Extract Inlined Constant bnd => "".
Extract Inlined Constant errorM_bind => "(@@)".
Extract Inlined Constant mbind => "(@@)".

(*Handle state monad*)
Extraction NoInline new_ctr.
Extract Constant ctr_unit => "Why3OCaml.BigInt.t ref".
Extract Constant ctr "'ty" => "'ty".
Extract Inlined Constant ctr_ret => "".
Extract Inlined Constant ctr_bnd' => "(@@)".
Extract Inlined Constant ctr_bnd => "(@@)".
Extract Inlined Constant new_ctr => "ref Why3OCaml.BigInt.zero".
Extract Inlined Constant incr => "(id_ctr := Why3OCaml.BigInt.succ !id_ctr)".
Extract Inlined Constant ctr_get => "!id_ctr".
(*Extract Inlined Constant extract_ctr => "
  (fun f => let (i, x) = f !r in r:= i; x)".*)

(*NOTE: ctr a = int -> (int, a), say we have f,
  want let (i, x) = f !r in
    r := i;
    x*)


(*Definition ctr (a: Type) : Type := CoqBigInt.t -> CoqBigInt.t * a.

(*Note: should not be used directly*)
Definition ctr_get : ctr CoqBigInt.t := fun x => (x, x).

Definition ctr_ret {a: Type} (x: a) : ctr a := fun s => (s, x).
Definition ctr_bnd {a b: Type} (f: a -> ctr b) (x: ctr a) : ctr b :=
  fun i =>
    let t := x i in
    f (snd t) (fst t).

Definition new_ctr : ctr unit := fun _ => (CoqBigInt.zero, tt).
Definition incr : ctr unit := fun i => (CoqBigInt.succ i, tt).*)

(*Maps - inline some things to reduce dependent types, Obj.magic
  and unecessary functions*)
Extraction Inline gmap_car.
Extraction Inline gmap_empty.

(*Let's try TODO constrs*)
Extract Inductive ty_c => "ty_node_c ty_o" [ "mk_ty_o" ].
Extract Inductive tysymbol_c => "(ty_node_c ty_o) tysymbol_o" 
  ["(fun (a,b,c) -> build_tysym_o a b c)"]. (*need this for differences between Coq and Ocaml records, as per Zulip*)
Extract Inductive type_def_c => "(ty_node_c ty_o) type_def_o" 
  ["NoDef" "Alias" "Range" "Float"].
Extract Inlined Constant node_of_ty => "ty_node".
Extract Inlined Constant tag_of_ty => "ty_tag".
Extract Inlined Constant ident_of_tysym => "ts_name".
Extract Inlined Constant vars_of_tysym => "ts_args".
Extract Inlined Constant type_def_of_tysym => "ts_def".
Extract Inlined Constant type_def_trans => "". (*trivial id function*)


(*Definition ty := ty_o ty_node_c.
Definition tysymbol := tysymbol_o ty.
Definition type_def := type_def_o ty.*)


(*Extract Inductive ty_node__ => "ty_node_" ["Tyvar" "Tyapp"].*)
(*Extraction Inline ty'.
Extraction Inline tysymbol'.*)

(*Extraction Inline ty_build.
Extraction Inline ty_build'.
Extraction Inline ty_build_simpl.
Extraction Inline ty_build_simpl'.*)
Extraction Inline Decision RelDecision.

(*Unset Extraction Optimize.*)

Separate Extraction
  Extmap Extset Ty Ident. (*Ty.ty_v_map Ident.*)
(*Separate Extraction Extmap.
Separate Extraction Ty.ty Ty.ty_v_map Ident.*)

(*Recursive Extraction Library Ty.*)