From Src.core Require Import IdentDefs TyDefs TyFuncs.
From Src.util Require Import Extmap Extset Hashcons Ctr.
From stdpp Require Import gmap.
From Coq Require Extraction.
From ExtLib Require Import Monads EitherMonad StateMonad.

Extraction Blacklist String List Option.

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
Extract Inlined Constant CoqBigInt.compare => "BigInt.compare".
Extract Inlined Constant CoqBigInt.hash => "BigInt.hash".
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
Extract Inlined Constant CoqInt.zero => "Int.zero".
Extract Inlined Constant CoqInt.one => "Int.one".
Extract Inlined Constant CoqInt.neg_one => "Int.minus_one".
Extract Inlined Constant Hashcons.int_65599 => "65599".

Extract Inlined Constant CoqBigInt.to_Z => "ZCompat.to_Z_big".
Extract Inlined Constant CoqBigInt.of_Z => "ZCompat.of_Z_big".

(*TODO: this is BAD - figure out better*)
(*Extract Inlined Constant length => "List.length".
Extract Inlined Constant Coq.Arith.PeanoNat.Nat.eqb => "Int.equal".*)

(*Handle exception monad*)

Extract Constant errorM "'a" => "'a".
(*Extract Inductive errorM => " " ["Normal" "Error"] .  *)
Extract Inductive errtype => exn [""].
Extract Inlined Constant Not_found => "Not_found".
Extract Inlined Constant Invalid_argument => "Invalid_argument".
Extract Inlined Constant Exit => "Exit".
Extract Inlined Constant err_ret => "".
Extract Inlined Constant throw => "raise".
Extract Inlined Constant err_bnd => "(@@)".
Extraction Inline Monad_errorM.
(*Extraction Inline Monad_either.*)
(*Extract Inlined Constant ExtLib.MonadExn.raise => "raise".*)
(*TODO: see*)

Extract Inlined Constant mbind => "(@@)".

(*Handle state monad*)
Extract Inlined Constant ctr_ty => "BigInt.t ref".
(*Extract Constant state "'a" "'ty" => "'ty".*) (*TODO: ExtLib*)
(*Extract Inlined Constant st_ret => "".
Extract Inlined Constant st_bnd => "(@@)".*)
(*NOTE: we cannot extract get, set directly because
  they refer to different references each time*)
(*Extract Inlined Constant st_multi_ret => "".
Extract Inlined Constant exceptT_bnd => "(@@)".*)
Extract Constant ctr "'ty" => "'ty".
Extract Inlined Constant ctr_ret => "".
Extract Inlined Constant ctr_bnd => "(@@)".
Extract Inlined Constant new_ctr => "ref".
Extract Inlined Constant ctr_incr => "(ctr_ref := BigInt.succ !ctr_ref)".
(*Extract Inlined Constant incr => "(id_ctr := BigInt.succ !id_ctr)".*)
Extract Inlined Constant ctr_get => "!ctr_ref".
Extract Inlined Constant ctr_set => "fun x -> ctr_ref := x".

(*Handle hashcons*)
(*TODO: change this*)
Extract Constant hashcons_unit "'k" => 
  "(BigInt.t * 'k CoqHashtbl.hashset) ref".
Extract Constant hashcons_st "'ty" "'ty2" => "'ty2".
Extract Inlined Constant hashcons_ret => "".
Extract Inlined Constant hashcons_bnd => "(@@)".
Extract Inlined Constant hashcons_new => 
  "ref (BigInt.one, CoqHashtbl.create_hashset)".
Extract Inlined Constant hashcons_getset =>
  "(snd !hash_st)".
Extract Inlined Constant hashcons_get_ctr =>
  "(fst !hash_st)".
Extract Inlined Constant hashcons_incr => 
  "(let old = !hash_st in
    hash_st := (BigInt.succ (fst old), (snd old)))".
Extract Inlined Constant hashcons_lookup =>
  "(fun _ _ k -> CoqHashtbl.find_opt_hashset H.hash H.equal (snd !hash_st) k)".
Extract Inlined Constant hashcons_add =>
  "(fun _ k -> let old = !hash_st in
              hash_st := (fst old, CoqHashtbl.add_hashset H.hash (snd old) k))".

(*Hashcons + Exception Monad Transformer*)
Extract Constant errorHashconsT "'ty" "'ty2" => "'ty2".
Extract Inlined Constant errorHashcons_ret => "".
Extract Inlined Constant errorHashcons_bnd => "(@@)".
Extract Inlined Constant errorHashcons_lift => "".
Extraction Inline Monad_errorHashconsT.
Extraction Inline Exception_errorHashconsT.
Extract Inlined Constant errorHashcons_lift2 => "".
(*Print state.
(*TEMP*)
Definition snd_ty (A B: Type) : Type := B.
Extract Inductive state => "snd_ty" [""].*)

(*Hash table state monad*)
Extract Constant hash_st "'ty" "'ty2" "'ty3" => "'ty3".
(*Extraction Inline hash_st.*)
(*TODO: for all ret and bnd, inline and extract to 1 (if that works)*)
Extract Inlined Constant hash_ret => "".
Extract Inlined Constant hash_bnd => "(@@)".
Extract Constant hash_unit "'k" "'v" => "(('k, 'v) CoqHashtbl.hashtbl) ref".
Extract Inlined Constant hash_set => "(fun x -> hash_ref := x)".
Extract Inlined Constant hash_get => "!hash_ref".
Extract Inlined Constant new_hash => "ref CoqHashtbl.create_hashtbl".



(*Hash table + Exception Monad Transformer*)
Extract Constant errorHashT "'ty" "'ty2" "'ty3" => "'ty3".
Extract Inlined Constant errorHash_ret => "".
Extract Inlined Constant errorHash_bnd => "(@@)".
Extract Inlined Constant errorHash_lift => "".
Extraction Inline Monad_errorHashT.
Extraction Inline Exception_errorHashT.
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
Extract Inlined Constant BadTypeArity => "BadTypeArity".
Extract Inlined Constant DuplicateTypeVar => "DuplicateTypeVar".
Extract Inlined Constant UnboundTypeVar => "UnboundTypeVar".
Extract Inlined Constant IllegalTypeParameters => "IllegalTypeParameters".
Extract Inlined Constant EmptyRange => "EmptyRange".
Extract Inlined Constant BadFloatSpec => "BadFloatSpec".
Extract Inlined Constant UnexpectedProp => "UnexpectedProp".
Extract Inlined Constant TypeMismatch => "TypeMismatch".
Extraction Inline mk_errtype.
(*Extract Inlined Constant BadTypeArity_reg => "exception Exceptions.BadTypeArity of tysymbol * int".*)

(*Unset Extraction Optimize.*)

Separate Extraction
  Extmap Extset CoqHashtbl IdentDefs TyDefs TyFuncs. (*Ty.ty_v_map Ident.*)
(*Separate Extraction Extmap.
Separate Extraction Ty.ty Ty.ty_v_map Ident.*)

(*Recursive Extraction Library Ty.*)