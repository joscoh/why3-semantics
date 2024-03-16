From Src.core Require Import Ident TyDefs TyFuncs.
From Src.util Require Import Extmap Extset Hashcons.
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
Extract Inlined Constant CoqBigInt.t => "BigInt.t".
Extract Inlined Constant CoqBigInt.zero => "BigInt.zero" (*TODO: change to BigInt when put in Why3*).
Extract Inlined Constant CoqBigInt.one => "BigInt.one" (*TODO*).
Extract Inlined Constant CoqBigInt.succ => "BigInt.succ".
Extract Inlined Constant CoqBigInt.eqb => "BigInt.eq".
Extract Inlined Constant CoqBigInt.mul_int => "BigInt.mul_int".
Extract Inlined Constant CoqBigInt.add => "BigInt.add".
Extract Inlined Constant CoqBigInt.lt => "BigInt.lt".
Extract Inlined Constant CoqBigInt.two => "(BigInt.of_int 2)".
Extract Inlined Constant CoqBigInt.three => "(BigInt.of_int 3)".
Extract Inlined Constant CoqBigInt.four => "(BigInt.of_int 4)".
Extract Inlined Constant CoqBigInt.five => "(BigInt.of_int 5)".
Extract Inlined Constant CoqBigInt.six => "(BigInt.of_int 6)".
Extract Inlined Constant CoqBigInt.seven => "(BigInt.of_int 7)".
Extract Inlined Constant CoqBigInt.eight => "(BigInt.of_int 8)".
Extract Inlined Constant CoqBigInt.nine => "(BigInt.of_int 9)".

Extract Inlined Constant CoqInt.int => "Int.t".
Extract Inlined Constant CoqInt.int_eqb => "Int.equal".
Extract Inlined Constant Hashcons.int_65599 => "65599".

(*TODO: this is BAD - figure out better*)
Extract Inlined Constant length => "List.length".
Extract Inlined Constant Coq.Arith.PeanoNat.Nat.eqb => "Int.equal".

(*Handle exception monad*)

Extract Inductive errorM => " " ["Normal" "Error"] .  
Extract Inductive errtype => exn [""].
Extract Inlined Constant Not_found => "Not_found".
Extract Inlined Constant Invalid_argument => "Invalid_argument".
Extract Inlined Constant Exit => "Exit".
Extract Inlined Constant ret => "".
Extract Inlined Constant throw => "raise".
(*TODO: see*)
Extract Inlined Constant bnd => "".
Extract Inlined Constant errorM_bind => "(@@)".
Extract Inlined Constant mbind => "(@@)".

(*Handle state monad*)
Extract Constant ctr_unit => "BigInt.t ref".
Extract Constant ctr "'ty" => "'ty".
Extract Inlined Constant ctr_ret => "".
Extract Inlined Constant ctr_bnd' => "(@@)".
Extract Inlined Constant ctr_bnd => "(@@)".
Extract Inlined Constant new_ctr => "ref (BigInt.of_int 8)".
Extract Inlined Constant incr => "(id_ctr := BigInt.succ !id_ctr)".
Extract Inlined Constant ctr_get => "!id_ctr".

(*Handle hashcons*)

Extract Constant hashcons_unit "'k" => 
  "(BigInt.t * 'k Hashtbl.hashtbl) ref".
Extract Constant hashcons_st "'ty" "'ty2" => "'ty2".
Extract Inlined Constant hashcons_ret => "".
Extract Inlined Constant hashcons_bnd => "(@@)".
Extract Inlined Constant hashcons_new => 
  "ref (BigInt.one, Hashtbl.create_hashtbl)".
Extract Inlined Constant hashcons_incr => 
  "(let old = !hash_st in
    hash_st := (BigInt.succ (fst old), (snd old)))".
Extract Inlined Constant hashcons_get_ctr =>
  "(fst !hash_st)".
Extract Inlined Constant hashcons_lookup =>
  "(fun _ _ k -> Hashtbl.find_opt_hashtbl H.hash H.equal (snd !hash_st) k)".
Extract Inlined Constant hashcons_add =>
  "(fun _ k -> let old = !hash_st in
              hash_st := (fst old, Hashtbl.add_hashtbl H.hash (snd old) k))".

(*Hashcons + Exception Monad Transformer*)
Extract Constant errorHashT "'ty" "'ty2" => "'ty2".
Extract Inlined Constant errorHash_ret => "".
Extract Inlined Constant errorHash_bnd => "(@@)".
Extract Inlined Constant errorHash_lift => "".
Extract Inlined Constant errorHash_lift2 => "".

(*Maps - inline some things to reduce dependent types, Obj.magic
  and unecessary functions*)
Extraction Inline gmap_car.
Extraction Inline gmap_empty.

(*Extract ty to mixed record-inductive*)
Extract Inductive ty_c => "ty_node_c ty_o" 
  [ "(fun (a, b) -> build_ty_o a b)" ].
Extract Inductive tysymbol_c => "(ty_node_c ty_o) tysymbol_o" 
  ["(fun (a,b,c) -> build_tysym_o a b c)"]. (*need this for differences between Coq and Ocaml records, as per Zulip*)
Extract Inlined Constant ty_node_of => "ty_node".
Extract Inlined Constant ty_tag_of => "ty_tag".
Extract Inlined Constant ts_name_of => "ts_name".
Extract Inlined Constant ts_args_of => "ts_args".
Extract Inlined Constant ts_def_of => "ts_def".

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

(*Other exceptions*)
Extract Inlined Constant BadTypeArity => "TyExn.BadTypeArity".
Extract Inlined Constant DuplicateTypeVar => "TyExn.DuplicateTypeVar".
Extract Inlined Constant UnboundTypeVar => "TyExn.UnboundTypeVar".
Extract Inlined Constant IllegalTypeParameters => "TyExn.IllegalTypeParameters".
Extract Inlined Constant EmptyRange => "TyExn.EmptyRange".
Extract Inlined Constant BadFloatSpec => "TyExn.BadFloatSpec".
(*Extract Inlined Constant BadTypeArity_reg => "exception Exceptions.BadTypeArity of tysymbol * int".*)

(*Unset Extraction Optimize.*)

Separate Extraction
  Extmap Extset Hashtbl Ident TyDefs TyFuncs. (*Ty.ty_v_map Ident.*)
(*Separate Extraction Extmap.
Separate Extraction Ty.ty Ty.ty_v_map Ident.*)

(*Recursive Extraction Library Ty.*)