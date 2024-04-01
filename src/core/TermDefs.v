Require Import Ident.
Require Import Ty.
Require Import CoqWstdlib.
Require Import Monads.
Import MonadNotations.
Local Open Scope monad_scope.
Require Import IntFuncs.
(* Variable Symbols*)

Record vsymbol := {
  vs_name : ident;
  vs_ty : ty_c
}.

Definition vsymbol_eqb (v1 v2: vsymbol) : bool :=
  id_equal v1.(vs_name) v2.(vs_name) &&
  ty_equal v1.(vs_ty) v2.(vs_ty).

Lemma vsymbol_eqb_eq (v1 v2: vsymbol): v1 = v2 <-> vsymbol_eqb v1 v2.
Proof.
  unfold vsymbol_eqb.
  destruct v1 as [n1 t1]; destruct v2 as [n2 t2]; simpl.
  rewrite andb_true, <- ident_eqb_eq, <- ty_eqb_eq.
  solve_eqb_eq.
Qed.

Module VsymTag <: TaggedType.
Definition t := vsymbol.
Definition tag vs := vs.(vs_name).(id_tag).
Definition equal := vsymbol_eqb.
End VsymTag.

Module Vsym := MakeMSWeak(VsymTag).
Module Svs := Vsym.S.
Module Mvs := Vsym.M.

(*NOTE: (==) in OCaml*)
Definition vs_equal := vsymbol_eqb.
Definition vs_hash vs := id_hash vs.(vs_name).
Definition vs_compare vs1 vs2 := id_compare vs1.(vs_name) vs2.(vs_name).

Definition create_vsymbol (name: preid) (t: ty_c) : ctr vsymbol :=
  i <- id_register name ;;
  st_ret {| vs_name := i; vs_ty := t |}.

(*Function and Predicate Symbols*)
Record lsymbol := {
  ls_name : ident;
  ls_args : list ty_c;
  ls_value : option ty_c;
  ls_constr : CoqBigInt.t; (*is the symbol a constructor?*)
  ls_proj : bool (*TODO what is this?*)
}.

Definition lsymbol_eqb (l1 l2: lsymbol) : bool :=
  id_equal l1.(ls_name) l2.(ls_name) &&
  list_eqb ty_equal l1.(ls_args) l2.(ls_args) &&
  option_eqb ty_equal l1.(ls_value) l2.(ls_value) &&
  CoqBigInt.eqb l1.(ls_constr) l2.(ls_constr) &&
  Bool.eqb l1.(ls_proj) l2.(ls_proj).

(*TODO: move*)
Lemma bool_eqb_eq (b1 b2: bool) : b1 = b2 <-> Bool.eqb b1 b2.
Proof.
  symmetry.
  apply eqb_true_iff.
Qed.

Lemma lsymbol_eqb_eq (l1 l2: lsymbol) : l1 = l2 <-> lsymbol_eqb l1 l2.
Proof.
  unfold lsymbol_eqb.
  destruct l1 as [n1 a1 v1 c1 p1]; destruct l2 as [n12 a2 v2 c2 p2]; simpl.
  (*TODO: typeclasses? Or just tactic?*)
  rewrite !andb_true, <- ident_eqb_eq, <- CoqBigInt.eqb_eq,
    <- bool_eqb_eq, <- (list_eqb_eq ty_eqb_eq), <- (option_eqb_eq ty_eqb_eq).
  solve_eqb_eq.
Qed.

Module LsymTag <: TaggedType.
Definition t := lsymbol.
Definition tag ls := ls.(ls_name).(id_tag).
Definition equal := lsymbol_eqb.
End LsymTag.

Module Lsym := MakeMSWeak(LsymTag).
Module Sls := Lsym.S.
Module Mls := Lsym.M.

(*== in OCaml*)
Definition ls_equal (l1 l2: lsymbol) : bool := lsymbol_eqb l1 l2.
Definition ls_hash ls := id_hash ls.(ls_name).
Definition ls_compare ls1 ls2 := id_compare ls1.(ls_name) ls2.(ls_name).

(*Not sure why OCaml version also takes in args (unused)*)
(*Says that constructor cannot have type Prop*)
Definition check_constr (constr: CoqBigInt.t) (value : option ty_c) : 
  errorM CoqBigInt.t :=
  if CoqBigInt.is_zero constr || (CoqBigInt.pos constr && (isSome value))
  then err_ret constr
  else throw (Invalid_argument "Term.create_lsymbol").

(*I guess a proj is a non-constructor with only 1 argument?
  I think it is a record projection (but cant tell where it is used)*)
Definition check_proj (proj: bool) (constr: CoqBigInt.t) 
  (args: list ty_c) (value: option ty_c) : errorM bool :=
  if negb proj || (CoqBigInt.is_zero constr && (isSome value) && 
    CoqBigInt.eqb (int_length args) CoqBigInt.one)
  then err_ret proj 
  else throw (Invalid_argument "Term.create_lsymbol").

(*We do not have optional/labelled arguments, so we produce 2 versions
  leaving the current one (for now)*)
(*TODO: see if we need other versions*)
Definition create_lsymbol1 (name: preid) (args: list ty_c) 
  (value: option ty_c) : ctr lsymbol :=
  i <- id_register name ;;
  st_ret {| ls_name := i; ls_args := args; ls_value := value;
    ls_constr := CoqBigInt.zero; ls_proj := false |}.

Definition create_fsymbol1 nm al vl :=
  create_lsymbol1 nm al (Some vl).

Definition create_psymbol nm al :=
  create_lsymbol1 nm al None.

(*Type free vars both from arguments and return type*)
Definition ls_ty_freevars (ls: lsymbol) : Stv.t :=
  let acc := oty_freevars Stv.empty ls.(ls_value) in
  fold_left ty_freevars ls.(ls_args) acc.
