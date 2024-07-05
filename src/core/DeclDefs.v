Require Import CoqInt TyDefs TermDefs IdentDefs.

(*JOSH TODO: HORRIBLE HACK*)
(*Coq's extraction does not know that tysymbol_c -> tysymbol_o
  requires importing TyDefs, so it does not, and then can't find
  the result. So we have this completely fake definition in here
  so that Coq will import Ty in extraction.
  TODO: make it so we manually add files to import, probably delete
  from extracted code (maybe)*)
Definition hack : Type := tysymbol.

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

(*TODO: Spr, Mpr, etc*)
(*TODO: pr_equal, pr_hash, create_prsymbol*)

Definition ind_decl : Type := lsymbol * list (prsymbol * term).

(*TODO: we do not support Coind*)
Variant ind_sign := Ind | Coind.

Definition ind_list : Type := ind_sign * list ind_decl.

(*Proposition Declaraion*)
Variant prop_kind :=
  | Plemma (*prove, use as premise*)
  | Paxiom (*do not prove, use as premise*)
  | Pgoal (*prove, do not use as premise*)
  .

(*TODO: MOVE*)

Definition prop_decl : Type := ocaml_tup3 prop_kind prsymbol term.

(* Declaration Type *)

Variant decl_node :=
  | Dtype : tysymbol_c -> decl_node (*Abstract types and aliases*)
  | Ddata: list data_decl -> decl_node (*Recursive ADTs*)
  | Dparam : lsymbol -> decl_node (*abstract fun/pred*)
  | Dlogic : list logic_decl -> decl_node (*recursive fun/pred*)
  | Dind : ind_list -> decl_node (*(co) inductive predicates*)
  | Dprop : prop_decl -> decl_node (*axiom/lemma/goal*)
  .

Record decl := mk_decl { 
  d_node : decl_node;
  d_news : Sid.t;
  d_tag : CoqWeakhtbl.tag}.

(*Decidable Equality*)
Definition constructor_eqb : constructor -> constructor -> bool :=
  tuple_eqb ls_equal (list_eqb (option_eqb ls_equal)).

Definition data_decl_eqb : data_decl -> data_decl -> bool :=
  tuple_eqb ts_equal (list_eqb constructor_eqb).

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