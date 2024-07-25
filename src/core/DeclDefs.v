Require Import CoqInt TyDefs TermDefs TermFuncs IdentDefs CoqWstdlib.
Import MonadNotations.
Set Bullet Behavior "Strict Subproofs".

(*Type Declaration*)

(*Constructor symbol with the list of projections*)
Definition constructor : Type := lsymbol * list (option lsymbol).

Definition data_decl : Type := tysymbol_c * list constructor.

(*Logic Declaration*)

(*TODO: BigInt?*)
(*Ah, the last one is the terminating arguments - in our
  case, we want an int I believe*)
Definition ls_defn : Type := lsymbol * term_c * list CoqBigInt.t.

Definition logic_decl : Type := lsymbol * ls_defn.

(* Inductive Predicate declaration *)
Record prsymbol := { pr_name : ident }.

Definition prsymbol_eqb (p1 p2: prsymbol) : bool :=
  id_equal p1.(pr_name) p2.(pr_name).

Lemma prsymbol_eqb_eq p1 p2: p1 = p2 <-> prsymbol_eqb p1 p2.
Proof.
  destruct p1 as [i1]; destruct p2 as [i2]; unfold prsymbol_eqb; simpl.
  rewrite <- ident_eqb_eq. solve_eqb_eq.
Qed.

Module PropTag <: TaggedType.
Definition t := prsymbol.
Definition tag pr := pr.(pr_name).(id_tag).
Definition equal := prsymbol_eqb.
End PropTag.

Module Prop1 := MakeMSWeak PropTag.
Module Spr := Prop1.S.
Module Mpr := Prop1.M.

Definition pr_equal := prsymbol_eqb.
Definition pr_hash pr := id_hash pr.(pr_name).
Definition create_prsymbol n : ctr prsymbol := 
  (i <- id_register n ;;
  st_ret {| pr_name := i |})%state.

Definition ind_decl : Type := lsymbol * list (prsymbol * term_c).

(*TODO: we do not support Coind*)
Variant ind_sign := Ind | Coind.

Definition ind_list : Type := ind_sign * list ind_decl.

(*Proposition Declaraion*)
Variant prop_kind :=
  | Plemma (*prove, use as premise*)
  | Paxiom (*do not prove, use as premise*)
  | Pgoal (*prove, do not use as premise*)
  .

Definition prop_decl : Type := ocaml_tup3 prop_kind prsymbol term_c.

(* Declaration Type *)

Variant decl_node :=
  | Dtype : tysymbol_c -> decl_node (*Abstract types and aliases*)
  | Ddata: list data_decl -> decl_node (*Recursive ADTs*)
  | Dparam : lsymbol -> decl_node (*abstract fun/pred*)
  | Dlogic : list logic_decl -> decl_node (*recursive fun/pred*)
  | Dind : ind_list -> decl_node (*(co) inductive predicates*)
  | Dprop : prop_decl -> decl_node (*axiom/lemma/goal*)
  .

Record decl := build_decl { 
  d_node : decl_node;
  d_news : Sid.t;
  d_tag : CoqWeakhtbl.tag}.

(*Decidable Equality*)
Section Equality. 

Definition constructor_eqb : constructor -> constructor -> bool :=
  tuple_eqb ls_equal (list_eqb (option_eqb ls_equal)).

Definition data_decl_eqb : data_decl -> data_decl -> bool :=
  tuple_eqb ts_equal (list_eqb constructor_eqb).

Scheme Equality for ind_sign.
Scheme Equality for prop_kind.

Definition ind_sign_eqb := ind_sign_beq.
Definition prop_kind_eqb := prop_kind_beq.

Definition ls_defn_eqb : ls_defn -> ls_defn -> bool :=
  tuple_eqb (tuple_eqb ls_equal term_eqb) (list_eqb CoqBigInt.eqb).

Definition logic_decl_eqb : logic_decl -> logic_decl -> bool :=
  tuple_eqb ls_equal ls_defn_eqb.

Definition ind_decl_eqb : ind_decl -> ind_decl -> bool :=
  tuple_eqb ls_equal (list_eqb (tuple_eqb prsymbol_eqb term_eqb)).

(*Almost the same as hashcons equivalent but not quite.
  Hashcons does not care about all components of [logic_decl].
  Also, we need strict equality and not equality modulo alpha equiv *)
Definition decl_node_eqb (d1 d2: decl_node) : bool :=
  match d1, d2 with
  | Dtype s1, Dtype s2 => ts_equal s1 s2
  | Ddata l1, Ddata l2 => list_eqb data_decl_eqb l1 l2
  | Dparam s1, Dparam s2 => ls_equal s1 s2
  | Dlogic l1, Dlogic l2 => list_eqb logic_decl_eqb l1 l2
  | Dind (s1, l1), Dind (s2, l2) => ind_sign_eqb s1 s2 &&
    list_eqb ind_decl_eqb l1 l2
  | Dprop p1, Dprop p2 =>
    let '(k1, pr1, f1) := of_tup3 p1 in
    let '(k2, pr2, f2) := of_tup3 p2 in
    prop_kind_eqb k1 k2 && pr_equal pr1 pr2 && term_eqb f1 f2
  | _, _ => false
  end.

Definition decl_eqb (d1 d2: decl) : bool :=
  decl_node_eqb d1.(d_node) d2.(d_node) &&
  Sid.equal d1.(d_news) d2.(d_news) &&
  CoqWeakhtbl.tag_equal d1.(d_tag) d2.(d_tag).

(*And the proofs*) 
Lemma constructor_eqb_eq c1 c2:
  c1 = c2 <-> constructor_eqb c1 c2.
Proof.
  apply tuple_eqb_spec.
  - apply lsymbol_eqb_eq.
  - apply list_eqb_eq, option_eqb_eq, lsymbol_eqb_eq.
Qed.

Lemma data_decl_eqb_eq d1 d2:
  d1 = d2 <-> data_decl_eqb d1 d2.
Proof.
  apply tuple_eqb_spec.
  - apply tysymbol_eqb_eq.
  - apply list_eqb_eq, constructor_eqb_eq.
Qed.

Lemma ind_sign_eqb_eq i1 i2:
  i1 = i2 <-> ind_sign_eqb i1 i2.
Proof.
  split; intros.
  - apply internal_ind_sign_dec_lb; auto.
  - apply internal_ind_sign_dec_bl; auto.
Qed.

Lemma prop_kind_eqb_eq p1 p2:
  p1 = p2 <-> prop_kind_eqb p1 p2.
Proof.
  split; intros.
  - apply internal_prop_kind_dec_lb; auto.
  - apply internal_prop_kind_dec_bl; auto.
Qed.

Lemma ls_defn_eqb_eq l1 l2:
  l1 = l2 <-> ls_defn_eqb l1 l2.
Proof.
  apply tuple_eqb_spec.
  - intros. apply tuple_eqb_spec.
    + apply lsymbol_eqb_eq.
    + apply term_eqb_eq.
  - apply list_eqb_eq, CoqBigInt.eqb_eq.
Qed. 

Lemma logic_decl_eqb_eq l1 l2:
  l1 = l2 <-> logic_decl_eqb l1 l2.
Proof.
  apply tuple_eqb_spec.
  - apply lsymbol_eqb_eq.
  - apply ls_defn_eqb_eq.
Qed.

Lemma ind_decl_eqb_eq i1 i2:
  i1 = i2 <-> ind_decl_eqb i1 i2.
Proof.
  apply tuple_eqb_spec.
  - apply lsymbol_eqb_eq.
  - apply list_eqb_eq, tuple_eqb_spec.
    + apply prsymbol_eqb_eq.
    + apply term_eqb_eq.
Qed.

Lemma decl_node_eqb_eq d1 d2:
  d1 = d2 <-> decl_node_eqb d1 d2.
Proof.
  destruct d1 as [| | | | i1 |p1]; destruct d2 as [| | | | i2 |p2]; unfold decl_node_eqb; simpl; 
  try solve[solve_eqb_eq]; try solve[destruct i1; solve_eqb_eq];
  [rewrite <- tysymbol_eqb_eq | 
   rewrite <- (list_eqb_eq data_decl_eqb_eq) |
   rewrite <- lsymbol_eqb_eq |
   rewrite <- (list_eqb_eq logic_decl_eqb_eq) |
   | ]; try solve[solve_eqb_eq].
  - destruct i1; destruct i2.
    rewrite andb_true, <- ind_sign_eqb_eq, <- (list_eqb_eq ind_decl_eqb_eq).
    solve_eqb_eq.
  - destruct (of_tup3 p1) as [[k1 pr1] f1] eqn : Htup1.
    destruct (of_tup3 p2) as [[k2 pr2] f2] eqn : Htup2.
    (*A bit trickier because we cannot break OCaml abstraction*)
    rewrite !andb_true. rewrite <- prop_kind_eqb_eq, <- prsymbol_eqb_eq, <- term_eqb_eq.
    (*Need to solve manually*)
    split; intros Heq.
    + inversion Heq; subst. rewrite Htup1 in Htup2. inversion Htup2; auto.
    + destruct_all; subst.
      f_equal. apply of_tup3_inj. rewrite Htup1, Htup2. reflexivity.
Qed.

Lemma decl_eqb_eq d1 d2:
  d1 = d2 <-> decl_eqb d1 d2.
Proof.
  destruct d1 as [d1 s1 t1]. destruct d2 as [d2 s2 t2].
  unfold decl_eqb; simpl.
  rewrite !andb_true, <- decl_node_eqb_eq, <- Sid.equal_eq, 
  (*TODO: breaks abstraction, add to CoqWeakhtbl*)
  <- CoqBigInt.eqb_eq; [solve_eqb_eq |].
  apply ident_eqb_eq.
Qed.

End Equality.

(*Hash-consing*)
Module DeclHash <: hashcons.HashedType.

Definition t := decl.
(*Weaker than structural equality; ignore tags and metadata*)

Definition eq_ld (x1 x2: logic_decl) : bool :=
  ls_equal (fst x1) (fst x2) &&
  t_equal_strict (snd (fst (snd x1))) (snd (fst (snd x2))).

Definition eq_iax :=
  tuple_eqb pr_equal t_equal_strict.

Definition eq_ind1 : ind_decl-> ind_decl -> bool :=
  tuple_eqb ls_equal (list_eqb eq_iax).


Definition equal (d1 d2: decl) : bool :=
  match d1.(d_node), d2.(d_node) with
  | Dtype s1, Dtype s2 => ts_equal s1 s2
  | Ddata l1, Ddata l2 => list_eqb data_decl_eqb l1 l2
  | Dparam s1, Dparam s2 => ls_equal s1 s2
  | Dlogic l1, Dlogic l2 => list_eqb eq_ld l1 l2
  | Dind (s1, l1), Dind (s2, l2) => ind_sign_eqb s1 s2 &&
    list_eqb eq_ind1 l1 l2
  | Dprop p1, Dprop p2 =>
    let '(k1, pr1, f1) := of_tup3 p1 in
    let '(k2, pr2, f2) := of_tup3 p2 in
    prop_kind_eqb k1 k2 && pr_equal pr1 pr2 && t_equal_strict f1 f2
  | _, _ => false
  end.

(*Hashing - similar*)
Definition cs_hash (x: constructor) : CoqBigInt.t :=
  hashcons.combine_big_list (hashcons.combine_big_option ls_hash) 
    (ls_hash (fst x)) (snd x).

Definition hs_td (x: data_decl) : CoqBigInt.t :=
  hashcons.combine_big_list cs_hash (ts_hash (fst x)) (snd x).

Definition hs_ld (x: logic_decl) : CoqBigInt.t :=
  hashcons.combine_big (ls_hash (fst x)) (t_hash_strict (snd (fst (snd x)))).

Definition hs_prop (x: prsymbol * term_c) : CoqBigInt.t :=
  hashcons.combine_big (pr_hash (fst x)) (t_hash_strict (snd x)).

Definition hs_ind (x: ind_decl) : CoqBigInt.t :=
  hashcons.combine_big_list hs_prop (ls_hash (fst x)) (snd x).

Definition hs_kind (p: prop_kind) : CoqBigInt.t :=
  match p with
  | Plemma => CoqBigInt.eleven
  | Paxiom => CoqBigInt.thirteen
  | Pgoal => CoqBigInt.seventeen
  end.

Definition hash (d: decl) : CoqBigInt.t :=
  match d.(d_node) with
  | Dtype s => ts_hash s
  | Ddata l => hashcons.combine_big_list hs_td (CoqBigInt.three) l
  | Dparam s => ls_hash s
  | Dlogic l => hashcons.combine_big_list hs_ld CoqBigInt.five l
  | Dind (_, l) => hashcons.combine_big_list hs_ind CoqBigInt.seven l
  | Dprop y => let '(k, pr, f) := of_tup3 y in
    hashcons.combine_big (hs_kind k) (hs_prop (pr, f))
  end.

Definition tag (n: CoqWeakhtbl.tag) (d: decl) : decl :=
  {| d_node := d.(d_node); d_news := d.(d_news);
    d_tag := (CoqWeakhtbl.create_tag n)|}.

End DeclHash.

Module Hsdecl := hashcons.Make DeclHash.

Module DeclTag <: TaggedType.
Definition t := decl.
Definition tag d := d.(d_tag).
(*TODO: We cannot use reference equality, but can we just
  compare tags? TODO TRY THIS!
  For now, use decidable equality, which is much slower*)
Definition equal := decl_eqb.
End DeclTag.

Module Decl1 := MakeMSWeak DeclTag.
Module Sdecl := Decl1.S.
Module Mdecl := Decl1.M.

(*TODO: see note above (note: it will make proofs harder,
  we will have to expose both but we need to do anyway
  e.g. for term)*)
Definition d_equal := decl_eqb.
Definition d_hash d := CoqWeakhtbl.tag_hash d.(d_tag).

(*Declaration Constructors*)

Definition mk_decl (node: decl_node) (news: Sid.t) : 
  st (hashcons_ty decl) decl :=
  let d := {| d_node := node; 
    d_news := news; 
    d_tag := CoqWeakhtbl.dummy_tag |} in
  match node with
  | Dprop p =>
    let '(x, _, _) := of_tup3 p in
    match x with
    | Pgoal => Hsdecl.unique d
    | _ => Hsdecl.hashcons d
    end
  | _ => Hsdecl.hashcons d
  end.