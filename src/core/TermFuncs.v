Require Import IntFuncs Monads TyDefs TermDefs TyFuncs.
Import MonadNotations.
Local Open Scope monad_scope.

(*h-consing constructors for patterns*)

(*Exceptions*)
Definition UncoveredVar (v: vsymbol) : errtype :=
  mk_errtype "UncoveredVar" v.
Definition DuplicateVar (v: vsymbol) : errtype :=
  mk_errtype "DuplicateVar" v.

Definition mk_pattern (n: pattern_node) (vs: Svs.t) (t : ty_c) : pattern_c :=
  mk_pat_c n vs t.

Definition pat_wild (t: ty_c) : pattern_c :=
  mk_pattern Pwild Svs.empty t.

Definition pat_var (v: vsymbol) : pattern_c :=
  mk_pattern (Pvar v) (Svs.singleton v) v.(vs_ty).

Definition pat_as_aux (p: pattern_c) (v: vsymbol) : errorM pattern_c :=
  s <-- Svs.add_new (DuplicateVar v) v (pat_vars_of p) ;;
  err_ret (mk_pattern (Pas p v) s v.(vs_ty)).

Definition pat_or_aux (p q: pattern_c) : errorM pattern_c :=
  if Svs.equal (pat_vars_of p) (pat_vars_of q) then
    err_ret (mk_pattern (Por p q) (pat_vars_of p) (pat_ty_of p))
  else
    let s := Mvs.union _ (fun _ _ _ => None) (pat_vars_of p) (pat_vars_of q) in
    x <-- Svs.choose s ;;
    throw (UncoveredVar x).

(*A bit different implementation than OCaml because we cannot
  throw an exception during the merge.
  We first check for duplicate vars, then separately merge the sets.
  If we ever encounter an error, this will propagate via
  the semantics of bind*)

Definition pat_app_aux (f: lsymbol) (pl: list pattern_c) (t: ty_c) :
  errorM pattern_c :=
  (*Create 2 sets: 1 is union of all, other checks for duplicates*)
  let dups : errorM Svs.t := fold_left (fun (s : errorM Svs.t) p => 
    (*Check for common elts*)
    s1 <-- s ;;
    let dups := Mvs.inter (fun _ _ _ => Some tt) s1 (pat_vars_of p) in
    if negb (Mvs.is_empty _ dups) then
      x <-- Mvs.choose _ dups ;;
      throw (DuplicateVar (fst x))
    else
    (*Compute union*)
    err_ret (Mvs.union _ (fun _ _ _ => None) s1 (pat_vars_of p))
  ) pl (err_ret Svs.empty) in

  s <-- dups ;;
  err_ret (mk_pattern (Papp f pl) s t).

(* Generic Traversal Functions *)
Definition pat_map_aux (fn: pattern_c -> errorM pattern_c) (p: pattern_c) : errorM pattern_c :=
  match (pat_node_of p) with
  | Pwild => err_ret p
  | Pvar _ => err_ret p
  | Papp s pl =>
    l <-- errorM_list (map fn pl) ;;
    pat_app_aux s l (pat_ty_of p)
  | Pas p v => 
    p1 <-- fn p ;;
    pat_as_aux p1 v
  | Por p q => 
    p1 <-- fn p ;;
    q1 <-- fn q ;;
    pat_or_aux p1 q1
  end.

(*TODO: include monad?*)
Definition pat_map (fn: pattern_c -> pattern_c): pattern_c -> errorM pattern_c  :=
  pat_map_aux (fun p => 
    let res := fn p in
    _ <-- ty_equal_check (pat_ty_of p) (pat_ty_of res) ;;
    err_ret res).

Definition pat_fold {A: Type} (fn: A -> pattern_c -> A) (acc: A) (pat: pattern_c) : A :=
  match (pat_node_of pat) with
  | Pwild => acc
  | Pvar _ => acc
  | Papp _ pl => fold_left fn pl acc
  | Pas p _ => fn acc p
  | Por p q => fn (fn acc p) q
  end.

Definition pat_all (pr: pattern_c -> bool) (pat: pattern_c) : bool :=
  pat_fold (fun x y => x && (pr y)) true pat.

Definition pat_any (pr: pattern_c -> bool) (pat: pattern_c) : bool :=
  pat_fold (fun x y => x || (pr y)) false pat.

(* Smart Constructors for Patterns *)
Definition BadArity (x: lsymbol * CoqBigInt.t) : errtype :=
  mk_errtype "BadArity" x.
Definition FunctionSymbolExpected (l: lsymbol) : errtype :=
  mk_errtype "FunctionSymbolExpected" l.
Definition PredicateSymbolExpected (l: lsymbol) : errtype :=
  mk_errtype "PredicateSymbolExpected" l.
Definition ConstructorExpected (l: lsymbol) : errtype :=
  mk_errtype "ConstructorExpected" l.

(*TODO: bad*)
Fixpoint fold_left2_errorHashcons {A B C S : Type} 
  (f: C -> A -> B -> errorHashconsT S C) (accu: C) 
  (l1: list A) (l2: list B) : errorHashconsT S (option C) :=
  match l1, l2 with
  | nil, nil => errst_lift2 (err_ret (Some accu))
  | a1 :: l1, a2 :: l2 => 
    x <-- (f accu a1 a2) ;;;
    fold_left2_errorHashcons f x l1 l2
  | _, _ => errst_lift2 (err_ret None)
  end.

(*We need to do all of this because we include the types in
  everything, so we check for consistency*)
(*This gets ugly with the state (from ty_match)*)
Definition pat_app (fs: lsymbol) (pl: list pattern_c) (t: ty_c) : 
  errorHashconsT _ pattern_c :=
  (*First, make sure that the result types are matchable
    (i.e. list int vs list a maps a to int)*)
  s <-- (match fs.(ls_value) with
            | Some vty => ty_match Mtv.empty vty t
            | None => errst_lift2 (throw (FunctionSymbolExpected fs))
  end) ;;;
  let mtch s ty p := ty_match s ty (pat_ty_of p) in
  o <-- fold_left2_errorHashcons mtch s fs.(ls_args) pl ;;;
  errst_lift2 (match o with
  | None => throw (BadArity (fs, int_length pl))
  | Some _ => if CoqBigInt.is_zero fs.(ls_constr) then throw (ConstructorExpected fs)
  else pat_app_aux fs pl t
  end) 
  .

Definition pat_as (p: pattern_c) (v: vsymbol) : errorM pattern_c :=
  _ <-- ty_equal_check (pat_ty_of p) v.(vs_ty) ;;
  pat_as_aux p v.

Definition pat_or (p q: pattern_c) : errorM pattern_c :=
  _ <-- ty_equal_check (pat_ty_of p) (pat_ty_of q) ;;
  pat_or_aux p q.