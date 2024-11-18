From Src.core Require Import IdentDefs TyDefs TyFuncs TermDefs TermFuncs TermTraverse
DeclDefs DeclFuncs CoercionDefs TheoryDefs TheoryFuncs TaskDefs TaskFuncs TransDefs
PatternComp.
From Src.transform Require Import EliminateInductive EliminateDefinition.
From Src.coqutil Require Import IntFuncs CoqCtr State.
From Src.util Require Import ConstantDefs NumberFuncs extmap extset hashcons CoqExthtbl.
From Coq Require Extraction.
From ExtLib Require Import Monads EitherMonad StateMonad.

Extraction Blacklist Nat String List Option Bool Strings.

Require Import Coq.extraction.ExtrOcamlBasic.
(*Extract to native OCaml strings*)
Require Import Coq.extraction.ExtrOcamlNativeString.

Set Extraction KeepSingleton.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

Extract Inlined Constant proj_sumbool => "".

(*OCaml tuples*)
Extract Constant ocaml_tup3 "'a" "'b" "'c" => "'a * 'b * 'c".
Extract Inlined Constant to_tup3 => "(fun ((x, y), z) -> (x, y, z))".
Extract Inlined Constant of_tup3 => "(fun (x, y, z) -> ((x, y), z))".

(*Axiomatize OCaml ints and BigInts*)
(*TODO: move to approprate files?*)
(*TODO: We need this module stuff for now because dune does not
  support (include_subdirs unqualified) with Coq*)
Extract Inlined Constant CoqBigInt.t => "BigInt.t".
Extract Inlined Constant CoqBigInt.zero => "BigInt.zero".
Extract Inlined Constant CoqBigInt.one => "BigInt.one".
Extract Inlined Constant CoqBigInt.succ => "BigInt.succ".
Extract Inlined Constant CoqBigInt.pred => "BigInt.pred".
Extract Inlined Constant CoqBigInt.sub => "BigInt.sub".
Extract Inlined Constant CoqBigInt.mul => "BigInt.mul".
Extract Inlined Constant CoqBigInt.eqb => "BigInt.eq".
Extract Inlined Constant CoqBigInt.mul_int => "BigInt.mul_int".
Extract Inlined Constant CoqBigInt.add => "BigInt.add".
Extract Inlined Constant CoqBigInt.lt => "BigInt.lt".
Extract Inlined Constant CoqBigInt.is_zero => "BigInt.is_zero".
Extract Inlined Constant CoqBigInt.pos => "BigInt.pos".
Extract Inlined Constant CoqBigInt.compare => "BigInt.compare".
Extract Inlined Constant CoqBigInt.hash => "BigInt.hash".
Extract Inlined Constant CoqBigInt.min => "BigInt.min".
Extract Inlined Constant CoqBigInt.pow_int_pos_bigint => "BigInt.pow_int_pos_bigint".
Extract Inlined Constant CoqBigInt.of_int => "BigInt.of_int".
Extract Inlined Constant CoqBigInt.neg_one => "(BigInt.of_int (-1))".
Extract Inlined Constant CoqBigInt.two => "(BigInt.of_int 2)".
Extract Inlined Constant CoqBigInt.three => "(BigInt.of_int 3)".
Extract Inlined Constant CoqBigInt.four => "(BigInt.of_int 4)".
Extract Inlined Constant CoqBigInt.five => "(BigInt.of_int 5)".
Extract Inlined Constant CoqBigInt.six => "(BigInt.of_int 6)".
Extract Inlined Constant CoqBigInt.seven => "(BigInt.of_int 7)".
Extract Inlined Constant CoqBigInt.eight => "(BigInt.of_int 8)".
Extract Inlined Constant CoqBigInt.nine => "(BigInt.of_int 9)".
Extract Inlined Constant CoqBigInt.ten => "(BigInt.of_int 10)".
Extract Inlined Constant CoqBigInt.eleven => "(BigInt.of_int 11)".
Extract Inlined Constant CoqBigInt.thirteen => "(BigInt.of_int 13)".
Extract Inlined Constant CoqBigInt.seventeen => "(BigInt.of_int 17)".
Extract Inlined Constant CoqBigInt.nineteen => "(BigInt.of_int 19)".
Extract Inlined Constant CoqBigInt.to_string => "BigInt.to_string".

Extract Inlined Constant CoqInt.int => "Stdlib.Int.t".
Extract Inlined Constant CoqInt.int_eqb => "Stdlib.Int.equal".
Extract Inlined Constant CoqInt.zero => "Stdlib.Int.zero".
Extract Inlined Constant CoqInt.one => "Stdlib.Int.one".
Extract Inlined Constant CoqInt.two => "2". (*TODO: is constant OK?*)
Extract Inlined Constant CoqInt.five => "5". (*TODO: is constant OK?*)
Extract Inlined Constant CoqInt.neg_one => "Stdlib.Int.minus_one".
Extract Inlined Constant CoqInt.add => "Stdlib.Int.add".
Extract Inlined Constant CoqInt.mult => "Stdlib.Int.mul".
Extract Inlined Constant CoqInt.is_zero => "(fun x -> Stdlib.Int.equal x Stdlib.Int.zero)". 
Extract Inlined Constant hashcons.int_65599 => "65599".
Extract Inlined Constant CoqInt.compare => "Stdlib.Int.compare".
Extract Inlined Constant CoqInt.ge => "(fun x y -> Stdlib.Int.compare x y >= 0)".

Extract Inlined Constant CoqBigInt.to_Z => "ZCompat.to_Z_big".
Extract Inlined Constant CoqBigInt.of_Z => "ZCompat.of_Z_big".

Extract Inlined Constant string_compare => "String.compare".

(*For now*)
Extract Inlined Constant ident_eqb_fast => "(fun x y -> x == y || ident_eqb x y)".
Extract Inlined Constant tysymbol_eqb_fast => "(fun x y -> x == y || tysymbol_eqb x y)".
Extract Inlined Constant ty_eqb_fast => "(fun x y -> x == y || ty_eqb x y)".
Extract Inlined Constant pattern_eqb_fast => "(fun x y -> x == y || pattern_eqb x y)".
Extract Inlined Constant term_eqb_fast => "(fun x y -> x == y || term_eqb x y)".
Extract Inlined Constant term_branch_eqb_fast => "(fun x y -> x == y || term_branch_eqb x y)".
Extract Inlined Constant term_bound_eqb_fast => "(fun x y -> x == y || term_bound_eqb x y)".
Extract Inlined Constant term_quant_eqb_fast => "(fun x y -> x == y || term_quant_eqb x y)".
Extract Inlined Constant tdecl_eqb_fast => "(fun x y -> x == y || tdecl_eqb x y)".
Extract Inlined Constant meta_eqb_fast => "(fun x y -> x == y || meta_eqb x y)".
Extract Inlined Constant task_hd_eqb_fast => "(fun x y -> x == y || task_hd_eqb x y)".

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
Extract Inlined Constant st_ret => "(fun x -> x)".

(*Combine state monads*)
Extract Inlined Constant st_lift1 => "".
Extract Inlined Constant st_lift2 => "".

(*State + error monad*)
Extract Constant errState "'a" "'b" => "'b".
Extract Inlined Constant errst_bind => "(@@)".
Extract Inlined Constant errst_ret => "(fun x -> x)".
Extract Inlined Constant errst_lift1 => "".
Extract Inlined Constant errst_lift2 => "".
Extract Inlined Constant errst_tup1 => "".
Extract Inlined Constant errst_tup2 => "".
Extract Inlined Constant errst_assoc => "".
Extract Inlined Constant errst_congr1 => "". (*TODO: make sure OK*)
Extract Inlined Constant errst_bind_dep => "(fun x y -> y x () ())".


(*Mutable state monads*)
Extract Constant State.st_ty "'a" => "'a ref".
Extract Inlined Constant State.new_st => "ref".
Extract Inlined Constant State.st_set => "(fun x -> st_ref := x)".
Extract Inlined Constant State.st_get => "!st_ref".
Extract Inlined Constant State.st_run_UNSAFE => "(fun _ x -> st_ref := T.initial; x)".

(*Hashcons state monad lifts*)
Extract Inlined Constant full_of_ty => "".
Extract Inlined Constant full_of_d => "".
Extract Inlined Constant full_of_td => "".
Extract Inlined Constant full_of_tsk => "".
Extract Inlined Constant full_of_ty_d => "".
Extract Inlined Constant full_of_ty_td => "".
Extract Inlined Constant full_of_ty_tsk => "".
Extract Inlined Constant full_of_d_td => "".
Extract Inlined Constant full_of_d_tsk => "".
Extract Inlined Constant full_of_td_tsk => "".
Extract Inlined Constant full_of_ty_d_td => "".
Extract Inlined Constant full_of_ty_d_tsk => "".
Extract Inlined Constant full_of_ty_td_tsk => "".
Extract Inlined Constant full_of_d_td_tsk => "".

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

(*Extract pat to mixed record-inductive*)
Extract Inductive pattern_c => "(pattern_node pattern_o)" 
  [ "(fun (a, b, c) -> build_pattern_o a b c)" ].
Extract Inlined Constant pat_node_of => "pat_node".
Extract Inlined Constant pat_vars_of => "pat_vars".
Extract Inlined Constant pat_ty_of => "pat_ty".

(*Extract term to mixed record-inductive*)
Extract Inductive term_c => "(term_node term_o)"
  [ "(fun (a, b, c, d) -> build_term_o a b c d)"].
Extract Inlined Constant t_node_of => "t_node".
Extract Inlined Constant t_ty_of => "t_ty".
Extract Inlined Constant t_attrs_of => "t_attrs".
Extract Inlined Constant t_loc_of => "t_loc".

(*Extract namespace to solve positivity issue*)
Extract Inductive namespace_c => "namespace"
  ["(fun (x1, x2, x3, x4) -> make_namespace x1 x2 x3 x4)"].
Extract Inlined Constant make_namespace_c => "make_namespace".
Extract Inlined Constant ns_ts_of => "ns_ts".
Extract Inlined Constant ns_ls_of => "ns_ls".
Extract Inlined Constant ns_pr_of => "ns_pr".
Extract Inlined Constant ns_ns_of => "ns_ns".
Extract Inlined Constant ns_ns_alt => "(fun x -> mstr_to_pmap (ns_ns x))".
(*These functions must never be called*)
Extract Inlined Constant ns_ts1 => "failwith 'ns_ts1'".
Extract Inlined Constant ns_ls1 => "failwith 'ns_ls1'".
Extract Inlined Constant ns_pr1 => "failwith 'ns_pr1'".
Extract Inlined Constant ns_ns1 => "failwith 'ns_ns1'".

(*Extract theory to mixed record-inductive*)
Extract Inductive theory_c => "tdecl_node theory_o"
  ["(fun (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) -> build_theory_o x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)]"].
(*TODO: fun x => x.th_name? Then don't need to expose functions*)
Extract Inlined Constant th_name_of => "th_name".
Extract Inlined Constant th_path_of => "th_path".
Extract Inlined Constant th_decls_of => "th_decls".
Extract Inlined Constant th_ranges_of => "th_ranges".
Extract Inlined Constant th_floats_of => "th_floats".
Extract Inlined Constant th_ranges_alt => "(fun x -> mts_to_zmap (th_ranges x))".
Extract Inlined Constant th_floats_alt => "(fun x -> mts_to_zmap (th_floats x))".
Extract Inlined Constant th_crcmap_of => "th_crcmap".
Extract Inlined Constant th_proved_wf_of => "th_proved_wf".
Extract Inlined Constant th_export_of => "th_export".
Extract Inlined Constant th_known_of => "th_known".
Extract Inlined Constant th_local_of => "th_local".
Extract Inlined Constant th_used_of => "th_used".
Extract Inductive tdecl_c => "tdecl_node tdecl_o"
  ["(fun (x1, x2) -> build_tdecl_o x1 x2)"].
Extract Inlined Constant td_node_of => "td_node".
Extract Inlined Constant td_tag_of => "td_tag".

(*Other exceptions*)
Extract Inlined Constant BadTypeArity => "BadTypeArity".
Extract Inlined Constant DuplicateTypeVar => "DuplicateTypeVar".
Extract Inlined Constant UnboundTypeVar => "UnboundTypeVar".
Extract Inlined Constant IllegalTypeParameters => "IllegalTypeParameters".
Extract Inlined Constant EmptyRange => "EmptyRange".
Extract Inlined Constant BadFloatSpec => "BadFloatSpec".
Extract Inlined Constant UnexpectedProp => "UnexpectedProp".
Extract Inlined Constant TypeMismatch => "TypeMismatch".
Extract Inlined Constant OutOfRange => "OutOfRange".

(*Term exceptions*)
Extract Inlined Constant UncoveredVar => "UncoveredVar".
Extract Inlined Constant DuplicateVar => "DuplicateVar".
Extract Inlined Constant BadArity => "BadArity".
Extract Inlined Constant FunctionSymbolExpected => "FunctionSymbolExpected".
Extract Inlined Constant PredicateSymbolExpected => "PredicateSymbolExpected".
Extract Inlined Constant TermFuncs.ConstructorExpected => "ConstructorExpected".
Extract Inlined Constant TermExpected => "TermExpected".
Extract Inlined Constant FmlaExpected => "FmlaExpected".
Extract Inlined Constant AssertFail => "AssertFail".
Extract Inlined Constant InvalidIntegerLiteralType => "InvalidIntegerLiteralType".
Extract Inlined Constant InvalidRealLiteralType => "InvalidRealLiteralType".
Extract Inlined Constant InvalidStringLiteralType => "InvalidStringLiteralType".
Extract Inlined Constant EmptyCase => "EmptyCase".

(*Decl exceptions*)
Extract Inlined Constant UnboundVar => "UnboundVar".
Extract Inlined Constant UnexpectedProjOrConstr => "UnexpectedProjOrConstr".
Extract Inlined Constant NoTerminationProof => "NoTerminationProof".
Extract Inlined Constant IllegalTypeAlias=> "IllegalTypeAlias".
Extract Inlined Constant ClashIdent => "ClashIdent".
Extract Inlined Constant BadConstructor => "BadConstructor".
Extract Inlined Constant BadRecordField=> "BadRecordField".
Extract Inlined Constant RecordFieldMissing=> "RecordFieldMissing".
Extract Inlined Constant DuplicateRecordField=> "DuplicateRecordField".
Extract Inlined Constant EmptyDecl=> "EmptyDecl".
Extract Inlined Constant EmptyAlgDecl=> "EmptyAlgDecl".
Extract Inlined Constant EmptyIndDecl => "EmptyIndDecl".
Extract Inlined Constant NonPositiveTypeDecl => "(fun ((x, y), z) -> NonPositiveTypeDecl(x, y, z))".
Extract Inlined Constant BadLogicDecl => "BadLogicDecl".
Extract Inlined Constant InvalidIndDecl => "InvalidIndDecl".
Extract Inlined Constant NonPositiveIndDecl => "(fun ((x, y), z) -> NonPositiveIndDecl(x, y, z))".
Extract Inlined Constant KnownIdent => "KnownIdent".
Extract Inlined Constant UnknownIdent => "UnknownIdent".
Extract Inlined Constant RedeclaredIdent => "RedeclaredIdent".
Extract Inlined Constant NonFoundedTypeDecl => "NonFoundedTypeDecl".

(*Theory Exceptions*)
Extract Inlined Constant BadMetaArity => "BadMetaArity".
Extract Inlined Constant MetaTypeMismatch => "(fun ((x, y), z) -> MetaTypeMismatch (x, y, z))".


(*Task Exceptions*)
Extract Inlined Constant LemmaFound => "LemmaFound".
Extract Inlined Constant GoalFound => "GoalFound".
Extract Inlined Constant GoalNotFound => "GoalNotFound".

(*Pattern comp Exceptions*)
Extract Inlined Constant NonExhaustive => "NonExhaustive".
Extract Inlined Constant PatternComp.ConstructorExpected => "ConstructorExpected".
Extract Inlined Constant Failure => "Failure". (*TODO: MOVE*)


(*TODO: implement later*)
Extract Inlined Constant check_float => "Number.check_float".
(*Not implementing*)
Extract Inlined Constant pp_formattted_ty => "Pp.formatted".
Extract Inlined Constant pp_formatted_ty_eqb => "(=)".
(*Hash function, may implement*)
Extract Inlined Constant CoqWstdlib.string_hash => "(fun s -> (BigInt.of_int (Hashtbl.hash s)))".
(*Not implementing specific metas (yet) - requires state*)
Extract Inlined Constant meta_rewrite => "Compute.meta_rewrite".

Extraction Inline mk_errtype.

(*Try/Catch*)
(* We need to compare names for equality because
  we cannot just put e in the match, or else it is interpreted
  as a variable/wildcard*)
Extract Inlined Constant trywith => "(fun x e ret ->
  try x ()
  with | e1 -> if e = e1 then ret () else raise e1)".
Extract Inlined Constant errst_trywith => "(fun x e ret ->
  try x ()
  with | e1 -> if e = e1 then ret () else raise e1)".


(*Unset Extraction Optimize.*)
Separate Extraction (*CoqUtil.str_to_pos*) (*TEMP*)
  CoqExthtbl NumberDefs NumberFuncs hashcons extmap extset CoqHashtbl 
  CoqWstdlib
  ConstantDefs IdentDefs TyDefs TyFuncs TermDefs TermFuncs TermTraverse
  DeclDefs DeclFuncs CoercionDefs TheoryDefs TheoryFuncs TaskDefs TaskFuncs TransDefs
  EliminateInductive EliminateDefinition PatternComp.
(* TheoryDefs.*) (*Ty.ty_v_map Ident.*)
(*Separate Extraction Extmap.
Separate Extraction Ty.ty Ty.ty_v_map Ident.*)