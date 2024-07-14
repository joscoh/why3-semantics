(*The Theory API*)
From stdpp Require Import zmap gmap.  
Require Import CoqInt CoqWstdlib IdentDefs TyDefs TermDefs DeclDefs DeclFuncs 
  CoercionDefs.
(*We do NOT implement the theory API - we stop
  at the level of creating Tasks and proving transformations
  on Tasks correct. But we need the theory definitions because
  they are part of the Task definition*)


(** Namespace *)

(*Mstr.t namespace is not strictly positive so we will
  use a manual Zmap*)
(*Can we play a similar trick?*)

(*Translate*)
Definition gmap_to_mstr2 {A: Type} (z: gmap string A) : Mstr.t A :=
  gmap_fold _ Mstr.add Mstr.empty z. 
Definition mstr2_to_gmap {A: Type} (m: Mstr.t A) : gmap string A :=
  Mstr.fold (fun s x (acc : gmap string A) => <[s:=x]>acc) m gmap_empty.

Unset Elimination Schemes.
Inductive namespace_c := mk_namespace_c {
  ns_ts1 : Mstr.t tysymbol_c;   (* type symbols *)
  ns_ls1 : Mstr.t lsymbol;    (* logic symbols *)
  ns_pr1 : Mstr.t prsymbol;   (* propositions *)
  ns_ns1 : gmap string namespace_c;  (* inner namespaces *)
}.

(*OCaml version*)
Inductive namespace := mk_namespace {
  ns_ts : Mstr.t tysymbol_c;   (* type symbols *)
  ns_ls : Mstr.t lsymbol;    (* logic symbols *)
  ns_pr : Mstr.t prsymbol;   (* propositions *)
  ns_ns : Mstr.t namespace_c;  (* inner namespaces *)
}.
Set Elimination Schemes.

(*Constructors and Destructors*)

Definition make_namespace_o (ns_ts: Mstr.t tysymbol_c) 
  (ns_ls: Mstr.t lsymbol) (ns_pr: Mstr.t prsymbol)
  (ns_ns: Mstr.t namespace_c): namespace :=
  {| ns_ts := ns_ts; ns_ls := ns_ls; ns_pr := ns_pr; ns_ns := 
    ns_ns |}.

Definition make_namespace_c (ns_ts: Mstr.t tysymbol_c) 
  (ns_ls: Mstr.t lsymbol) (ns_pr: Mstr.t prsymbol)
  (ns_ns: Mstr.t namespace_c): namespace_c :=
  {| ns_ts1 := ns_ts; ns_ls1 := ns_ls; ns_pr1 := ns_pr; ns_ns1 := 
    mstr2_to_gmap ns_ns |}.

Definition ns_ts_of (n: namespace_c) : Mstr.t tysymbol_c :=
  ns_ts1 n.
Definition ns_ls_of (n: namespace_c) : Mstr.t lsymbol := ns_ls1 n.
Definition ns_pr_of (n: namespace_c) : Mstr.t prsymbol := ns_pr1 n.
Definition ns_ns_of (n: namespace_c) : Mstr.t namespace_c :=
  gmap_to_mstr2 (ns_ns1 n).

(** Meta properties *)

Variant meta_arg_type :=
  | MTty
  | MTtysymbol
  | MTlsymbol
  | MTprsymbol
  | MTstring
  | MTint
  | MTid.

Variant meta_arg :=
  | MAty: ty_c -> meta_arg
  | MAts: tysymbol_c -> meta_arg
  | MAls: lsymbol -> meta_arg
  | MApr : prsymbol -> meta_arg
  | MAstr: string -> meta_arg
  | MAint: CoqInt.int -> meta_arg
  | MAid: ident -> meta_arg.

(*NOTE: I am NOT dealing with formats. Will axiomatize this type;
  we will never require any properties of it*)
Axiom pp_formattted_ty : Type.

Record meta := {
  meta_name : string;
  meta_type : list meta_arg_type;
  meta_excl : bool;
  meta_desc : pp_formattted_ty; (*Pp.formatted;*)
  meta_tag  : CoqBigInt.t;
}.

(** Theory *)
Record symbol_map := {
  sm_ty : Mts.t ty_c;
  sm_ts : Mts.t tysymbol_c;
  sm_ls : Mls.t lsymbol;
  sm_pr : Mpr.t prsymbol;
}.

(*NOTE: we CANNOT use Mts.t tdecl_c, which is what we would want
  to use, because Coq cannot tell that this is strictly positive
  (due to the sigma type). Instead we will just use
  Zmap key tdecl_c and define functions we need in TheoryExtra
  This is really not great because we change the API.
  But it doesn't seem like people really use this part of Theory,
  including Why3 itself *)
Unset Elimination Schemes.

(*Now, the OCaml versions, with the same interface as existing*)
Record tdecl_o (A: Type) :=
{
  td_node : A;
  td_tag  : CoqBigInt.t;
}.

Record theory_o (A: Type) := {
  th_name   : ident;          (* theory name *)
  th_path   : list string;    (* environment qualifiers *)
  th_decls  : list (tdecl_o A);     (* theory declarations *)
  th_ranges : Mts.t (tdecl_o A);    (* range type projections *)
  th_floats : Mts.t (tdecl_o A);    (* float type projections *)
  th_crcmap : CoercionDefs.t;     (* implicit coercions *)
  th_proved_wf : Mls.t (prsymbol * lsymbol) ; (* predicates proved well-founded *)
  th_export : namespace_c;      (* exported namespace *)
  th_known  : known_map;      (* known identifiers *)
  th_local  : Sid.t;          (* locally declared idents *)
  th_used   : Sid.t;          (* used theories *)
}.

Inductive theory_c :=
  | mk_theory_c : 
    ident -> (*theory name*) 
    list string -> (* environment qualifiers *) 
    list tdecl_c -> (* theory declarations *)
    Zmap (tysymbol_c * tdecl_c) ->  (* range type projections *) 
    Zmap (tysymbol_c * tdecl_c) -> (* float type projections *) 
    CoercionDefs.t -> (* implicit coercions *) 
    Mls.t (prsymbol * lsymbol) ->  (* predicates proved well-founded *) 
    namespace_c -> (* exported namespace *) 
    known_map -> (* known identifiers *) 
    Sid.t -> (* locally declared idents *) 
    Sid.t -> (* used theories *) 
    theory_c
with tdecl_c :=
  | mk_tdecl_c : tdecl_node -> CoqBigInt.t -> tdecl_c
with tdecl_node :=
  | Decl: decl -> tdecl_node
  | Use: theory_c -> tdecl_node
  | Clone: theory_c -> symbol_map  -> tdecl_node
  | Meta : meta -> list meta_arg -> tdecl_node.

(*And a utility to ensure clients can have the same behavior*)
Definition proj_zmap_to_map {A: Type} (z: Zmap (tysymbol_c * A)) : 
  Mts.t A :=
  Zmap_fold _ (fun _ y acc => Mts.add (fst y) (snd y) acc) Mts.empty z.

Set Elimination Schemes.

Definition tdecl := tdecl_o tdecl_node.
Definition theory := theory_o tdecl_node.

(*Constructors and destructors*)
Section ExtractInterface.

(*Destructors*)
Definition th_name_of (th: theory_c) : ident :=
  match th with
  | mk_theory_c n _ _ _ _ _ _ _ _ _ _ => n
  end.

Definition th_path_of (th: theory_c) : list string :=
  match th with
  | mk_theory_c _ p _ _ _ _ _ _ _ _ _ => p
  end.

Definition th_decls_of (th: theory_c) : list tdecl_c :=
  match th with
  | mk_theory_c _ _ l _ _ _ _ _ _ _ _ => l
  end.

Definition th_ranges_of (th: theory_c) : Mts.t tdecl_c :=
  match th with
  | mk_theory_c _ _ _ r _ _ _ _ _ _ _ => proj_zmap_to_map r
  end.

Definition th_floats_of (th: theory_c) : Mts.t tdecl_c :=
  match th with
  | mk_theory_c _ _ _ _ f _ _ _ _ _ _ => proj_zmap_to_map f
  end.

Definition th_crcmap_of (th: theory_c) : CoercionDefs.t :=
  match th with
  | mk_theory_c _ _ _ _ _ c _ _ _ _ _ => c
  end.

Definition th_proved_wf_of (th: theory_c) : Mls.t (prsymbol * lsymbol) :=
  match th with
  | mk_theory_c _ _ _ _ _ _ p _ _ _ _ => p
  end.

Definition th_export_of (th: theory_c) : namespace_c :=
  match th with
  | mk_theory_c _ _ _ _ _ _ _ n _ _ _ => n
  end.

Definition th_known_of (th: theory_c) : known_map :=
  match th with
  | mk_theory_c _ _ _ _ _ _ _ _ k _ _ => k
  end.

Definition th_local_of (th: theory_c) : Sid.t :=
  match th with
  | mk_theory_c _ _ _ _ _ _ _ _ _ l _ => l
  end.

Definition th_used_of (th: theory_c) : Sid.t :=
  match th with
  | mk_theory_c _ _ _ _ _ _ _ _ _ _ u => u
  end.

Definition td_node_of (t: tdecl_c) : tdecl_node :=
  match t with
  | mk_tdecl_c t _ => t
  end.

Definition td_tag_of (t: tdecl_c) : CoqBigInt.t :=
  match t with
  | mk_tdecl_c _ z => z
  end.

(*Constructors*)
Definition build_tdecl_o (t: tdecl_node) (z: CoqBigInt.t) :
  tdecl :=
  {| td_node := t; td_tag := z |}.

Definition build_theory_o (th_name : ident) (th_path : list string)
  (th_decls : list tdecl) (th_ranges : Mts.t tdecl)
  (th_floats : Mts.t tdecl) (th_crcmap : CoercionDefs.t)
  (th_proved_wf : Mls.t (prsymbol * lsymbol))
  (th_export: namespace_c) (th_known: known_map)
  (th_local: Sid.t) (th_used : Sid.t) : theory :=
  {| th_name := th_name;
    th_path := th_path; th_decls := th_decls;
    th_ranges := th_ranges; th_floats := th_floats;
    th_crcmap := th_crcmap; th_proved_wf := th_proved_wf;
    th_export := th_export; th_known := th_known;
    th_local := th_local; th_used := th_used |}.

End ExtractInterface.
