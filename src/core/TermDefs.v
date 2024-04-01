Require Import Ident.
Require Import Ty.
Require Import CoqWstdlib.
Require Import Monads.
Import MonadNotations.
Local Open Scope monad_scope.
Require Import IntFuncs.
Set Bullet Behavior "Strict Subproofs".

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

(* Patterns *)

(*We use the same trick as with Ty, see notes there*)
Unset Elimination Schemes.
Record pattern_o (A: Type) :=
  {pat_node: A; pat_vars: Svs.t; pat_ty : ty_c}.

Inductive pattern_c :=
  | mk_pat_c : pattern_node -> Svs.t -> ty_c -> pattern_c
with pattern_node :=
  | Pwild
  | Pvar : vsymbol -> pattern_node
  | Papp: lsymbol -> list pattern_c -> pattern_node
  | Por: pattern_c -> pattern_c -> pattern_node
  | Pas : pattern_c -> vsymbol -> pattern_node.

Set Elimination Schemes.
Definition pattern := pattern_o pattern_node.

(*Again:To ensure that extraction results in correct code, we 
  should ONLY interact with record _c types through this interface*)
Section ExtractInterface.

Definition pat_node_of (p: pattern_c) : pattern_node :=
  match p with
  | mk_pat_c p _ _ => p
  end.

Definition pat_vars_of (p: pattern_c) : Svs.t :=
  match p with
  | mk_pat_c _ s _ => s
  end.

Definition pat_ty_of (p: pattern_c) : ty_c :=
  match p with
  | mk_pat_c _ _ t => t
  end.

(*Constructor*)
Definition build_pattern_o (p: pattern_node)
  (s: Svs.t) (t: ty_c) : pattern_o pattern_node :=
    {| pat_node := p; pat_vars := s; pat_ty := t |}.

End ExtractInterface.

(*TODO: go back and use this*)
Definition mk_Forall {A: Type} {P: A -> Prop} := 
  fun (f: forall x, P x) =>
    fix mk_Forall (l: list A) {struct l} : Forall P l :=
      match l with
      | nil => Forall_nil _
      | x :: xs => Forall_cons _ _ _ (f x) (mk_Forall xs)
      end.

(*Induction principle and decidable equality*)
Section PatInd.

Variable (P1: pattern_c -> Prop).
Variable (P2: pattern_node -> Prop).
Variable (Hpat: forall p, P2 (pat_node_of p) -> P1 p).
Variable (Hwild: P2 Pwild).
Variable (Hvar: forall v, P2 (Pvar v)).
Variable (Happ: forall l ps, Forall P1 ps -> P2 (Papp l ps)).
Variable (Hor: forall p1 p2, P1 p1 -> P1 p2 -> P2 (Por p1 p2)).
Variable (Has: forall p v, P1 p -> P2 (Pas p v)).

Fixpoint pattern_c_ind (p: pattern_c) : P1 p :=
  Hpat p (pattern_node_ind (pat_node_of p))
with pattern_node_ind (p: pattern_node) : P2 p :=
  match p with
  | Pwild => Hwild
  | Pvar v => Hvar v
  | Papp l ps => Happ l ps (mk_Forall pattern_c_ind ps)
  | Por p1 p2 => Hor p1 p2 (pattern_c_ind p1) (pattern_c_ind p2)
  | Pas p v => Has p v (pattern_c_ind p)
  end.

Definition pattern_mut_ind:
  (forall p, P1 p) /\ (forall p, P2 p) :=
  conj (fun p => pattern_c_ind p) (fun p => pattern_node_ind p).

End PatInd.

(*Decidable equality*)
Fixpoint pattern_eqb (p1 p2: pattern_c) : bool :=
  pattern_node_eqb (pat_node_of p1) (pat_node_of p2) &&
  Svs.equal (pat_vars_of p1) (pat_vars_of p2) &&
  ty_equal (pat_ty_of p1) (pat_ty_of p2)
with pattern_node_eqb (p1 p2: pattern_node) : bool :=
  match p1, p2 with
  | Pwild, Pwild => true
  | Pvar v1, Pvar v2 => vs_equal v1 v2
  | Papp l1 ps1, Papp l2 ps2 =>
    ls_equal l1 l2 &&
    CoqBigInt.eqb (int_length ps1) (int_length ps2) &&
    forallb (fun x => x) (map2 pattern_eqb ps1 ps2)
  | Por p1 p2, Por p3 p4 => pattern_eqb p1 p3 &&
    pattern_eqb p2 p4
  | Pas p1 v1, Pas p2 v2 => pattern_eqb p1 p2 &&
    vs_equal v1 v2
  | _, _ => false
  end.

Lemma pattern_eqb_rewrite p1 p2:
  pattern_eqb p1 p2 =
  match p1, p2 with
  | mk_pat_c p1 s1 t1, mk_pat_c p2 s2 t2 =>
    pattern_node_eqb p1 p2 &&
    Svs.equal s1 s2 &&
    ty_equal t1 t2
  end.
Proof.
  destruct p1; destruct p2; reflexivity.
Qed.

Lemma pattern_eqb_eq_aux:
  (forall p1 p2, p1 = p2 <-> pattern_eqb p1 p2) /\
  (forall p1 p2, p1 = p2 <-> pattern_node_eqb p1 p2).
Proof.
  apply pattern_mut_ind.
  - intros p IH p2.
    rewrite pattern_eqb_rewrite.
    destruct p as [p1 s1 t1]; destruct p2 as [p2 s2 t2].
    rewrite !andb_true, <- IH, <- ty_eqb_eq, 
      <- (Svs.equal_eq vsymbol_eqb_eq); simpl.
    solve_eqb_eq.
  - intros p2; destruct p2; simpl; solve_eqb_eq.
  - intros v p2; destruct p2; simpl; try rewrite <- vsymbol_eqb_eq;
    solve_eqb_eq.
  - intros l ps Hall p2. destruct p2 as [| | l2 ps2 | |];
    try solve[solve_eqb_eq].
    simpl.
    rewrite !andb_true.
    rewrite int_length_eq,<- nat_eqb_eq, <- lsymbol_eqb_eq,
    and_assoc, <- (forall_eqb_eq Hall).
    solve_eqb_eq.
  - intros p1 p2 IH1 IH2 [| | | p3 p4 |]; try solve[solve_eqb_eq];
    simpl.
    rewrite andb_true, <- IH1, <- IH2. solve_eqb_eq.
  - intros p v IH [| | | | p2 v2]; try solve[solve_eqb_eq]; simpl.
    rewrite andb_true, <- IH, <- vsymbol_eqb_eq.
    solve_eqb_eq.
Qed.

Definition pattern_eqb_eq := proj1 pattern_eqb_eq_aux.
Definition pattern_node_eqb_eq := proj2 pattern_eqb_eq_aux.

(*No sets/maps of patterns*)