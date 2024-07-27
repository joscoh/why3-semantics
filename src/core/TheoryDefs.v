(*The Theory API*)
From stdpp Require zmap gmap.
Require Import PmapExtra CoqInt CoqWstdlib.
Require Export IdentDefs TyDefs TermDefs CoercionDefs DeclDefs DeclFuncs.
Set Bullet Behavior "Strict Subproofs".
(*We do NOT implement the theory API - we stop
  at the level of creating Tasks and proving transformations
  on Tasks correct. But we need the theory definitions because
  they are part of the Task definition*)

Import zmap pmap.
(** Namespace *)

(*Mstr.t namespace is not strictly positive so we will
  use a manual Zmap*)
(*Zmap is much easier than gmap, we don't directly
  need extensionality, and we could prove ourselves
  if we needed*)
(*Translate*)
Definition pmap_to_mstr {A: Type} (z: Pmap (string * A)) : Mstr.t A :=
  Pmap_fold _ (fun _ y => Mstr.add (fst y) (snd y)) Mstr.empty z.
Definition mstr_to_pmap {A: Type} (m: Mstr.t A) : Pmap (string * A) :=
  Mstr.fold (fun s x (acc : Pmap (string * A)) => <[strings.string_to_pos s:=(s, x)]>acc) m Pmap_empty.

Unset Elimination Schemes.
Inductive namespace_c := mk_namespace_c {
  ns_ts1 : Mstr.t tysymbol_c;   (* type symbols *)
  ns_ls1 : Mstr.t lsymbol;    (* logic symbols *)
  ns_pr1 : Mstr.t prsymbol;   (* propositions *)
  ns_ns1 : Pmap (string * namespace_c);  (* inner namespaces *)
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
    mstr_to_pmap ns_ns |}.

Definition ns_ts_of (n: namespace_c) : Mstr.t tysymbol_c :=
  ns_ts1 n.
Definition ns_ls_of (n: namespace_c) : Mstr.t lsymbol := ns_ls1 n.
Definition ns_pr_of (n: namespace_c) : Mstr.t prsymbol := ns_pr1 n.
Definition ns_ns_of (n: namespace_c) : Mstr.t namespace_c :=
  pmap_to_mstr (ns_ns1 n).
(*For inductive definitions*)
Definition ns_ns_alt (n: namespace_c) :=
  ns_ns1 n.

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
Definition zmap_to_mts {A: Type} (z: Zmap (tysymbol_c * A)) : 
  Mts.t A :=
  Zmap_fold _ (fun _ y acc => Mts.add (fst y) (snd y) acc) Mts.empty z.

Definition mts_to_zmap {A: Type} (m: Mts.t A) : Zmap (tysymbol_c * A) :=
  Mts.fold (fun t y (acc : Zmap (tysymbol_c * A)) => 
    <[CoqBigInt.to_Z (CoqWeakhtbl.tag_hash (ts_name_of t).(id_tag)):=(t, y)]>acc) m Zmap_empty.

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
  | mk_theory_c _ _ _ r _ _ _ _ _ _ _ => zmap_to_mts r
  end.

Definition th_floats_of (th: theory_c) : Mts.t tdecl_c :=
  match th with
  | mk_theory_c _ _ _ _ f _ _ _ _ _ _ => zmap_to_mts f
  end.

(*For recursive definitions in Coq - extract to
  (mts_to_zmap) - otherwise Coq cannot tell struct decrease*)
Definition th_ranges_alt (th: theory_c) :=
  match th with
  | mk_theory_c _ _ _ r _ _ _ _ _ _ _ => r
  end.

Definition th_floats_alt (th: theory_c):=
  match th with
  | mk_theory_c _ _ _ _ f _ _ _ _ _ _ => f
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

(** Equality *)

(*Needed [gmap_eqb] because we do not yet have EqDecision for this type*)
Fixpoint namespace_eqb (n1 n2: namespace_c) {struct n1} : bool :=
  Mstr.equal ts_equal (ns_ts_of n1) (ns_ts_of n2) &&
  Mstr.equal ls_equal (ns_ls_of n1) (ns_ls_of n2) &&
  Mstr.equal pr_equal (ns_pr_of n1) (ns_pr_of n2) &&
  pmap_eqb (tuple_eqb String.eqb namespace_eqb) (ns_ns_alt n1) (ns_ns_alt n2) .

Scheme Equality for meta_arg_type.
Definition meta_arg_type_eqb := meta_arg_type_beq.

Definition meta_arg_eqb (m1 m2: meta_arg) : bool :=
  match m1, m2 with
  | MAty t1, MAty t2 => ty_equal t1 t2
  | MAts t1, MAts t2 => ts_equal t1 t2
  | MAls l1, MAls l2 => ls_equal l1 l2
  | MApr p1, MApr p2 => pr_equal p1 p2
  | MAstr s1, MAstr s2 => String.eqb s1 s2
  | MAint i1, MAint i2 => CoqInt.int_eqb i1 i2
  | MAid i1, MAid i2 => id_equal i1 i2
  | _, _ => false
  end.

(*TODO: ensure this is sound*)
Axiom pp_formatted_ty_eqb : pp_formattted_ty -> pp_formattted_ty -> bool.
Axiom pp_formatted_ty_eqb_eq: forall x y,
  x = y <-> pp_formatted_ty_eqb x y.

Definition meta_eqb (m1 m2: meta) : bool :=
(*Tag first*)
  CoqBigInt.eqb m1.(meta_tag) m2.(meta_tag) &&
  String.eqb m1.(meta_name) m2.(meta_name) &&
  list_eqb meta_arg_type_eqb m1.(meta_type) m2.(meta_type) &&
  Bool.eqb m1.(meta_excl) m2.(meta_excl) &&
  pp_formatted_ty_eqb m1.(meta_desc) m2.(meta_desc).

Definition symbol_map_eqb (s1 s2: symbol_map) : bool :=
  Mts.equal ty_eqb s1.(sm_ty) s2.(sm_ty) &&
  Mts.equal ts_equal s1.(sm_ts) s2.(sm_ts) &&
  Mls.equal ls_equal s1.(sm_ls) s2.(sm_ls) &&
  Mpr.equal pr_equal s1.(sm_pr) s2.(sm_pr).

(*Equality for tdecl*)

(*This is very annoying: cannot recurse under Mts
  so we need a size param
  TODO: what about zmap?*)

Fixpoint theory_eqb (t1 t2: theory_c) {struct t1} : bool :=
  id_equal (th_name_of t1) (th_name_of t2) &&
  list_eqb String.eqb (th_path_of t1) (th_path_of t2) &&
  list_eqb tdecl_eqb (th_decls_of t1) (th_decls_of t2) &&
  zmap_eqb (tuple_eqb ts_equal tdecl_eqb) (th_ranges_alt t1) (th_ranges_alt t2) &&
  zmap_eqb (tuple_eqb ts_equal tdecl_eqb) (th_floats_alt t1) (th_floats_alt t2) &&
  CoercionDefs.t_eqb (th_crcmap_of t1) (th_crcmap_of t2) &&
  Mls.equal (tuple_eqb pr_equal ls_equal)
    (th_proved_wf_of t1) (th_proved_wf_of t2) &&
  namespace_eqb (th_export_of t1) (th_export_of t2) &&
  Mid.equal d_equal (th_known_of t1) (th_known_of t2) &&
  Sid.equal (th_local_of t1) (th_local_of t2) &&
  Sid.equal (th_used_of t1) (th_used_of t2)
with tdecl_eqb (t1 t2: tdecl_c) {struct t1} : bool :=
  (*Important: tag is first*)
  CoqBigInt.eqb (td_tag_of t1) (td_tag_of t2) &&
  tdecl_node_eqb (td_node_of t1) (td_node_of t2)
with tdecl_node_eqb (t1 t2: tdecl_node) {struct t1} : bool :=
  match t1, t2 with
  | Decl d1, Decl d2 => d_equal d1 d2
  | Use t1, Use t2 => theory_eqb t1 t2
  | Clone t1 s1, Clone t2 s2 => theory_eqb t1 t2 &&
    symbol_map_eqb s1 s2  
  | Meta m1 a1, Meta m2 a2 => meta_eqb m1 m2 &&
    list_eqb meta_arg_eqb a1 a2
  | _, _ => false
  end.

(*Proofs*)

Definition prop_snd {A B: Type} {P: B -> Prop} : A * B -> Prop :=
  fun x => P (snd x).

Definition all_snd {A B: Type} {P: B -> Prop} (f: forall x, P x):
  forall (x: A * B), prop_snd x :=
  fun x => f (snd x).

(*TODO: move*)
Lemma list_eqb_Forall {A: Type} {eqb: A -> A -> bool} {l1: list A}
  (Hall: Forall (fun x => forall y, x = y <-> eqb x y) l1) l2:
  l1 = l2 <-> list_eqb eqb l1 l2.
Proof.
  revert l2. induction l1 as [| h1 t1 IH]; intros [| h2 t2]; simpl;
  try solve[solve_eqb_eq].
  rewrite andb_true, <- (Forall_inv Hall h2), <- IH;
  [solve_eqb_eq |].
  apply Forall_inv_tail in Hall; auto.
Qed.

(*Induction Principle for Namespace*)
Section NamespaceInd.
Variable (P: namespace_c -> Prop).
Variable (Hname: forall n, pmap_Forall (@prop_snd _ _ P) 
  (ns_ns_alt n) -> P n).

Fixpoint namespace_ind (n: namespace_c) : P n :=
  Hname n (mk_pmap_Forall (all_snd namespace_ind) (ns_ns_alt n)).

End NamespaceInd.

(*Induction Principle for Theories*)
Section TheoryInd.
(* Definition zmap_forall {A: Type} (p: A -> Prop) (z: Zmap A) : Prop :=
  Zmap_fold _ (fun _ x y => p x /\ y) True z. *)

Variable (P: theory_c -> Prop) (P1: tdecl_c -> Prop) (P2: tdecl_node -> Prop).
Variable (Htheory: forall (t: theory_c),
  Forall P1 (th_decls_of t) ->
  Zmap_Forall (fun x => P1 (snd x)) (th_ranges_alt t) ->
  Zmap_Forall (fun x => P1 (snd x)) (th_floats_alt t) ->
  P t).
Variable (Htdecl: forall (t: tdecl_c),
  P2 (td_node_of t) -> P1 t).
Variable (Hdecl: forall d, P2 (Decl d)).
Variable (Huse: forall t, P t -> P2 (Use t)).
Variable (Hclone: forall t1 s1, P t1 -> P2 (Clone t1 s1)).
Variable (Hmeta: forall m a, P2 (Meta m a)).

(*The induction principle is actually easy with all this*)
Fixpoint theory_ind (t: theory_c) : P t :=
  Htheory t (mk_Forall tdecl_ind (th_decls_of t))
    (mk_Zmap_Forall (all_snd tdecl_ind) (th_ranges_alt t))
    (mk_Zmap_Forall (all_snd tdecl_ind) (th_floats_alt t))
with tdecl_ind (t: tdecl_c) : P1 t :=
  Htdecl t (tdecl_node_ind (td_node_of t))
with tdecl_node_ind (t: tdecl_node) : P2 t :=
  match t with
  | Decl d => Hdecl d
  | Use th => Huse _ (theory_ind th)
  | Clone th syms => Hclone th syms (theory_ind th)
  | Meta m margs => Hmeta m margs
  end.

Definition theory_mut_ind:
  (forall t, P t) /\
  (forall t, P1 t) /\
  (forall t, P2 t) :=
  conj (fun t => theory_ind t)
    (conj (fun t => tdecl_ind t)
      (fun t => tdecl_node_ind t)).

End TheoryInd.

Lemma string_eqb_eq s1 s2:
  s1 = s2 <-> String.eqb s1 s2.
Proof.
  rewrite <- String.eqb_eq. reflexivity.
Qed.

(*Now prove equality*)
Lemma namespace_eqb_eq (n1 n2: namespace_c) :
  n1 = n2 <-> namespace_eqb n1 n2.
Proof.
  revert n2.
  apply namespace_ind with (P:=fun n1 => forall n2,
    n1 = n2 <-> namespace_eqb n1 n2).
  clear. intros [t1 l1 p1 n1] Hall [t2 l2 p2 n2];
  simpl in *.
  rewrite !andb_true.
  rewrite <- !(Mstr.eqb_eq _ prsymbol_eqb_eq string_eqb_eq),
  <- (Mstr.eqb_eq _ tysymbol_eqb_eq string_eqb_eq),
  <- (Mstr.eqb_eq _ lsymbol_eqb_eq string_eqb_eq).
  rewrite <- pmap_eqb_Forall; [solve_eqb_eq|].
  eapply pmap_Forall_impl; [apply Hall|].
  intros.
  destruct x as [s1 n1']; destruct y as [s2 n2'];
  unfold tuple_eqb; simpl.
  rewrite andb_true, <- string_eqb_eq, <- (H0 n2').
  simpl. solve_eqb_eq.
Qed.

Lemma symbol_map_eqb_eq s1 s2:
  s1 = s2 <-> symbol_map_eqb s1 s2.
Proof.
  destruct s1 as [t1 ty1 l1 p1]; destruct s2 as [t2 ty2 l2 p2];
  unfold symbol_map_eqb; simpl.
  rewrite !andb_true, <- (Mts.eqb_eq _ ty_eqb_eq tysymbol_eqb_eq),
  <- (Mts.eqb_eq _ tysymbol_eqb_eq tysymbol_eqb_eq),
  <- (Mls.eqb_eq _ lsymbol_eqb_eq lsymbol_eqb_eq),
  <- (Mpr.eqb_eq _ prsymbol_eqb_eq prsymbol_eqb_eq).
  solve_eqb_eq.
Qed.

Lemma meta_arg_type_eqb_eq m1 m2:
  m1 = m2 <-> meta_arg_type_eqb m1 m2.
Proof.
  split. apply internal_meta_arg_type_dec_lb.
  apply internal_meta_arg_type_dec_bl.
Qed.

Lemma meta_eqb_eq m1 m2:
  m1 = m2 <-> meta_eqb m1 m2.
Proof.
  destruct m1; destruct m2; unfold meta_eqb; simpl.
  rewrite !andb_true, <- string_eqb_eq, <-
  (list_eqb_eq meta_arg_type_eqb_eq),
  <- bool_eqb_eq, <- pp_formatted_ty_eqb_eq,
  <- CoqBigInt.eqb_eq. solve_eqb_eq.
Qed.

Lemma meta_arg_eqb_eq a1 a2:
  a1 = a2 <-> meta_arg_eqb a1 a2.
Proof.
  destruct a1; destruct a2; simpl; try solve[solve_eqb_eq];
  [rewrite <- ty_eqb_eq | rewrite <- tysymbol_eqb_eq |
   rewrite <- lsymbol_eqb_eq | rewrite <- prsymbol_eqb_eq |
   rewrite <- string_eqb_eq | unfold is_true; rewrite <- CoqInt.int_eqb_eq |
   rewrite <- ident_eqb_eq]; solve_eqb_eq.
Qed.

Lemma theory_eqb_eq_aux:
  (forall t1 t2, t1 = t2 <-> theory_eqb t1 t2) /\
  (forall t1 t2, t1 = t2 <-> tdecl_eqb t1 t2) /\
  (forall t1 t2, t1 = t2 <-> tdecl_node_eqb t1 t2).
Proof.
  apply theory_mut_ind.
  - intros t1 Hdecs Hranges Hfloats t2.
    destruct t1; destruct t2; simpl in *.
    rewrite !andb_true, <- ident_eqb_eq, <-
    (list_eqb_eq (fun x y => iff_sym (String.eqb_eq x y))).
    rewrite <- (list_eqb_Forall Hdecs).
    assert (Hforall2: forall z,
    Zmap_Forall (fun x => forall y, x.2 = y <-> tdecl_eqb x.2 y) z ->
    Zmap_Forall (fun x => forall y,
      x = y <-> tuple_eqb tysymbol_eqb tdecl_eqb x y) z
    ).
    {
      intros zm Hall. eapply Zmap_Forall_impl. apply Hall. simpl.
      intros.
      destruct x as [ts1 td1]; destruct y as [ts2 td2];
      unfold tuple_eqb; simpl in *.
      rewrite andb_true, <- tysymbol_eqb_eq, <- H0. solve_eqb_eq.
    }
    rewrite <- (zmap_eqb_Forall (Hforall2 _ Hranges)), 
    <- (zmap_eqb_Forall (Hforall2 _ Hfloats)), <- CoercionDefs.t_eqb_eq,
    <- (Mls.eqb_eq _ (tuple_eqb_spec _ _ prsymbol_eqb_eq lsymbol_eqb_eq) lsymbol_eqb_eq),
    <- namespace_eqb_eq, <- (Mid.eqb_eq _ decl_eqb_eq ident_eqb_eq),
    <- !(Sid.equal_eq ident_eqb_eq). clear.
    solve_eqb_eq.
  - intros [x1 y1] IH [x2 y2]; simpl in *.
    rewrite andb_true, <- IH, <- CoqBigInt.eqb_eq.
    solve_eqb_eq.
  - intros d t2; destruct t2; try solve[solve_eqb_eq].
    simpl. rewrite <- decl_eqb_eq. solve_eqb_eq.
  - intros th IH t2. destruct t2; try solve[solve_eqb_eq].
    simpl. rewrite <- IH. solve_eqb_eq.
  - intros th1 s1 IH t2. destruct t2; try solve[solve_eqb_eq].
    simpl. rewrite andb_true, <- IH, <- symbol_map_eqb_eq.
    solve_eqb_eq.
  - intros m a t2; destruct t2; try solve[solve_eqb_eq].
    simpl. rewrite andb_true, <- meta_eqb_eq,
    <- (list_eqb_eq meta_arg_eqb_eq). solve_eqb_eq.
Qed.

Definition theory_eqb_eq := proj1 theory_eqb_eq_aux.
Definition tdecl_eqb_eq := proj1 (proj2 theory_eqb_eq_aux).
Definition tdecl_node_eqb_eq := proj2 (proj2 theory_eqb_eq_aux).

(*Fast versions: in OCaml: fun x y -> (x == y) || eq x y
  If we choose tag first in eq, then should be almost as
  fast as == (assuming hashconsing) without additional proofs*)
Definition meta_eqb_fast := meta_eqb.
Definition tdecl_eqb_fast := tdecl_eqb.

Definition meta_equal : meta -> meta -> bool := meta_eqb_fast.
Definition meta_hash m := m.(meta_tag).

Module MetaTag <: TaggedType.
Definition t := meta.
Definition tag m := m.(meta_tag).
Definition equal := meta_eqb_fast.
End MetaTag.

Module SMmeta1 := MakeMS MetaTag.
Module Smeta := SMmeta1.S.
Module Mmeta := SMmeta1.M.


Module TdeclTag <: TaggedType.
Definition t := tdecl_c.
Definition tag td := td_tag_of td.
Definition equal := tdecl_eqb.
End TdeclTag.

Module Tdecl1 := MakeMS TdeclTag.

Module Stdecl1 := Tdecl1.S.
Module Mtdecl1 := Tdecl1.M.

Definition td_equal (t1 t2: tdecl_c) : bool := tdecl_eqb_fast t1 t2.
Definition td_hash (td: tdecl_c) := td_tag_of td.

(* Theory Declarations *)

Module TdeclHash <: hashcons.HashedType.
Definition t := tdecl_c.

(*Don't compare IDs*)
Definition eq_marg (m1 m2: meta_arg) : bool :=
  match m1, m2 with
  | MAty t1, MAty t2 => ty_equal t1 t2
  | MAts t1, MAts t2 => ts_equal t1 t2
  | MAls l1, MAls l2 => ls_equal l1 l2
  | MApr p1, MApr p2 => pr_equal p1 p2
  | MAstr s1, MAstr s2 => String.eqb s1 s2
  | MAint i1, MAint i2 => CoqInt.int_eqb i1 i2
  | _, _ => false
  end.

Definition eq_smap := symbol_map_eqb.

Definition equal td1 td2 := 
  match td_node_of td1, td_node_of td2 with
  | Decl d1, Decl d2 => d_equal d1 d2
  | Use th1, Use th2 => id_equal (th_name_of th1) (th_name_of th2)
  | Clone th1 sm1, Clone th2 sm2 =>
      id_equal (th_name_of th1) (th_name_of th2) && eq_smap sm1 sm2
  | Meta t1 al1, Meta t2 al2 =>
      meta_eqb_fast t1 t2 && list_eqb eq_marg al1 al2
  | _, _ => false
  end.

Definition hs_cl_ty {A: Type} (_: A) ty acc := 
  hashcons.combine_big acc (ty_hash ty).
Definition hs_cl_ts {A: Type} (_ : A) ts acc := 
  hashcons.combine_big acc (ts_hash ts).
Definition hs_cl_ls {A: Type} (_ : A) ls acc := 
  hashcons.combine_big acc (ls_hash ls).
Definition hs_cl_pr {A: Type} (_ : A) pr acc := 
  hashcons.combine_big acc (pr_hash pr).

Definition hs_ta x :=
  match x with 
  | MAty ty => ty_hash ty
  | MAts ts => ts_hash ts
  | MAls ls => ls_hash ls
  | MApr pr => pr_hash pr
  | MAstr s => string_hash s (*OK because we will not call this in Coq*)
  | MAint i => CoqBigInt.of_int i (*TODO: not real hash*) (*BigInt.of_int (Hashtbl.hash i)*)
  | MAid i => IdentDefs.id_hash i
  end.

Definition hs_smap (sm : symbol_map) (h: CoqBigInt.t) : CoqBigInt.t :=
  Mts.fold hs_cl_ty sm.(sm_ty)
    (Mts.fold hs_cl_ts sm.(sm_ts)
      (Mls.fold hs_cl_ls sm.(sm_ls)
        (Mpr.fold hs_cl_pr sm.(sm_pr) h))).

Definition hash (td : tdecl_c) : CoqBigInt.t :=  
  match td_node_of td with
  | Decl d => d_hash d 
  | Use th => id_hash (th_name_of th) 
  | Clone  th sm => hs_smap sm  (id_hash (th_name_of th))
  | Meta t al => hashcons.combine_big_list hs_ta (meta_hash t) al
  end.

Definition tag (n: CoqBigInt.t) td : tdecl_c :=
  mk_tdecl_c (td_node_of td) n.
End TdeclHash.

Module Hstdecl := hashcons.Make TdeclHash.

Definition mk_tdecl n : hashcons_st tdecl_c tdecl_c := Hstdecl.hashcons (mk_tdecl_c n CoqBigInt.neg_one).

Definition create_decl d := mk_tdecl (Decl d).
