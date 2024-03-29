From Src.core Require Import IdentDefs TyDefs TyFuncs.
From Src.coqutil Require Import Ctr.
From Src.util Require Import extmap extset hashcons CoqExthtbl.
(* From stdpp Require Import gmap.  *)
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
Extract Inlined Constant CoqBigInt.neg_one => "(BigInt.of_int (-1))".
Extract Inlined Constant CoqBigInt.two => "(BigInt.of_int 2)".
Extract Inlined Constant CoqBigInt.three => "(BigInt.of_int 3)".
Extract Inlined Constant CoqBigInt.four => "(BigInt.of_int 4)".
Extract Inlined Constant CoqBigInt.five => "(BigInt.of_int 5)".
Extract Inlined Constant CoqBigInt.six => "(BigInt.of_int 6)".
Extract Inlined Constant CoqBigInt.seven => "(BigInt.of_int 7)".
Extract Inlined Constant CoqBigInt.eight => "(BigInt.of_int 8)".
Extract Inlined Constant CoqBigInt.nine => "(BigInt.of_int 9)".

Extract Inlined Constant CoqInt.int => "Stdlib.Int.t".
Extract Inlined Constant CoqInt.int_eqb => "Stdlib.Int.equal".
Extract Inlined Constant CoqInt.zero => "Stdlib.Int.zero".
Extract Inlined Constant CoqInt.one => "Stdlib.Int.one".
Extract Inlined Constant CoqInt.neg_one => "Stdlib.Int.minus_one".
Extract Inlined Constant CoqInt.add => "Stdlib.Int.add".
Extract Inlined Constant CoqInt.mult => "Stdlib.Int.mul".
Extract Inlined Constant hashcons.int_65599 => "65599".

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

(*Monads*)

(*General state monad*)
Extract Constant st "'a" "'b" => "'b".
Extract Inlined Constant st_bind => "(@@)".
Extract Inlined Constant st_ret => "".

(*Combine state monads*)
Extract Inlined Constant st_lift1 => "".
Extract Inlined Constant st_lift2 => "".

(*State + error monad*)
Extract Constant errState "'a" "'b" => "'b".
Extract Inlined Constant errst_bind => "(@@)".
Extract Inlined Constant errst_ret => "".
Extract Inlined Constant errst_lift1 => "".
Extract Inlined Constant errst_lift2 => "".

(*Counter*)
Extract Inlined Constant ctr_ty => "BigInt.t ref".
Extract Inlined Constant new_ctr => "ref".
Extract Inlined Constant ctr_incr => "(ctr_ref := BigInt.succ !ctr_ref)".
Extract Inlined Constant ctr_get => "!ctr_ref".
Extract Inlined Constant ctr_set => "fun x -> ctr_ref := x".

(*Handle hashcons*)
Extract Constant hashcons_unit "'k" => 
  "(BigInt.t * 'k CoqHashtbl.hashset) ref".
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

(*Hash table state monad*)
Extract Constant hash_unit "'k" "'v" => "(('k, 'v) CoqHashtbl.hashtbl) ref".
Extract Inlined Constant hash_set => "(fun x -> hash_ref := x)".
Extract Inlined Constant hash_get => "!hash_ref".
Extract Inlined Constant new_hash => "ref CoqHashtbl.create_hashtbl".

(*Maps - inline some things to reduce dependent types, Obj.magic
  and unecessary functions*)
(*TODO: Fix (associativity issue)*)
(*Extraction Inline gmap_car.
Extraction Inline gmap_empty.*)

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
(*Extraction Inline Decision RelDecision.*)

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

Separate Extraction CoqUtil.str_to_pos (*TEMP*)
  CoqExthtbl CoqNumber hashcons extmap extset CoqHashtbl IdentDefs TyDefs TyFuncs. (*Ty.ty_v_map Ident.*)
(*Separate Extraction Extmap.
Separate Extraction Ty.ty Ty.ty_v_map Ident.*)

(*Recursive Extraction Library Ty.*)