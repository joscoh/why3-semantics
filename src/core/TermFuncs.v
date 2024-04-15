Require Import IntFuncs Monads TyDefs TermDefs TyFuncs IdentDefs.
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

(*Term equality modulo alpha-equivalence and location*)
Section TCompare.
Variable trigger attr loc const: bool.

Definition list_comp l : CoqInt.int :=
  fold_left lex_comp l CoqInt.zero.

(*Compare variables v1 and v2.
  To be equal, they must either be mapped to each other in each map
  or not in either map and equal*)
Definition var_compare (m1 m2: Mvs.t CoqBigInt.t) (v1 v2: vsymbol) : CoqInt.int :=
  match Mvs.find_opt _ v1 m1, Mvs.find_opt _ v2 m2 with
  | Some i1, Some i2 => CoqBigInt.compare i1 i2
  | None, None => vs_compare v1 v2
  | Some _, _ => CoqInt.neg_one
  | _, _ => CoqInt.one
  end.

Definition quant_compare (q1 q2: quant) : CoqInt.int :=
  match q1, q2 with
  | Tforall, Texists => CoqInt.neg_one
  | Texists, Tforall => CoqInt.one
  | _, _ => CoqInt.zero
  end.

Definition binop_compare (b1 b2: binop) : CoqInt.int :=
  match b1, b2 with
  | Tand, Tand => CoqInt.zero
  | Tor, Tor => CoqInt.zero
  | Timplies, Timplies => CoqInt.zero
  | Tiff, Tiff => CoqInt.zero
  | Tand, _ => CoqInt.neg_one
  | _, Tand => CoqInt.one
  | Tor, _ => CoqInt.neg_one
  | _, Tor => CoqInt.one
  | Timplies, _ => CoqInt.neg_one
  | _, Timplies => CoqInt.one
  end.


(*Version of fold_left2 with default values for shorter lists*)
(*Weird definition so Coq's termination checker accepts it*)
Definition fold_left2_def {A B C: Type} :=
  fun (f : A -> B -> C -> A) (d1 d2: A) =>
    fix fold_left2_def (l1: list B) : list C -> A -> A :=
      match l1 with
      | nil => fun l2 acc =>
        match l2 with
        | nil => acc
        | _ :: _ => d1
        end
      | x1 :: t1 => fun l2 acc =>
        match l2 with
        | nil => d2
        | x2 :: t2 => fold_left2_def t1 t2 (f acc x1 x2)
        end
      end.
    
(* Fixpoint fold_left2_def {A B C: Type} (f: A -> B -> C -> A) (acc: A)
  (l1: list B)(l2: list C) (d1 d2: A) : A :=
  match l1, l2 with
  | nil, nil => acc
  | x1 :: t1, x2 :: t2 => fold_left2_def f (f acc x1 x2) t1 t2 d1 d2
  | nil, _ :: _ => d1
  | _ :: _, nil => d2
  end. *)

(*TODO CHECK OCAML*)
(*Version of*)

(*TODO CHECK OCAML*)
Definition or_cmp_vsym (bv1 bv2: Mvs.t CoqBigInt.t) (v1 v2: vsymbol) :=
  match Mvs.find_opt _ v1 bv1, Mvs.find_opt _ v2 bv2 with
    | Some i1, Some i2 => CoqBigInt.compare i1 i2
    (*Should never happen*)
    | None, None => CoqInt.zero
    | Some _, None => CoqInt.neg_one
    | _, _ => CoqInt.one
  end.


Fixpoint or_cmp (bv1 bv2: Mvs.t CoqBigInt.t) (q1 q2: pattern_c) : CoqInt.int :=
  match (pat_node_of q1), (pat_node_of q2) with
  | Pwild, Pwild => CoqInt.zero
  | Pvar v1, Pvar v2 =>
    (*TODO CHECK OCAML*)
    or_cmp_vsym bv1 bv2 v1 v2
  | Papp s1 l1, Papp s2 l2 =>
    let i1 := ls_compare s1 s2 in
    lex_comp i1 (
      fold_left2_def (fun i p1 p2 =>
        lex_comp i (or_cmp bv1 bv2 p1 p2))
        CoqInt.neg_one CoqInt.one l1 l2
        CoqInt.zero 
    )
  | Por p1 q1, Por p2 q2 =>
    let i1 := or_cmp bv1 bv2 p1 p2 in
    lex_comp i1 (or_cmp bv1 bv2 q1 q2)
  | Pas p1 v1, Pas p2 v2 =>
    let i1 := or_cmp bv1 bv2 p1 p2 in
    lex_comp i1 (or_cmp_vsym bv1 bv2 v1 v2)
  | Pwild,  _ => CoqInt.neg_one | _, Pwild  => CoqInt.one
  | Pvar _, _ => CoqInt.neg_one | _, Pvar _ => CoqInt.one
  | Papp _ _, _ => CoqInt.neg_one | _, Papp _ _ => CoqInt.one
  | Por _ _,  _ => CoqInt.neg_one | _, Por _ _  => CoqInt.one
  end.

Fixpoint pat_compare (state: CoqBigInt.t * Mvs.t CoqBigInt.t * Mvs.t CoqBigInt.t)
  (p1 p2: pattern_c) : CoqInt.int * CoqBigInt.t * Mvs.t CoqBigInt.t * Mvs.t CoqBigInt.t :=
  let '(bnd, bv1, bv2) := state in
  match (pat_node_of p1), (pat_node_of p2) with
  | Pwild, Pwild => (CoqInt.zero, bnd, bv1, bv2)
  | Pvar v1, Pvar v2 => (CoqInt.zero, CoqBigInt.succ bnd, Mvs.add v1 bnd bv1, Mvs.add v2 bnd bv2) (*equal by fiat*)
  | Papp s1 l1, Papp s2 l2 =>
    let i1 := ls_compare s1 s2 in
    let '(sbnd, sm1, sm2) := state in
    let '(i2, bnd, bv1, bv2) := fold_left2_def (fun acc p1 p2 =>
      let '(i, bnd1, m1, m2) := acc in
      let '(j, bnd2, m1', m2') := pat_compare (bnd1, m1, m2) p1 p2 in
        (lex_comp i j, bnd2, m1', m2')) 
        (CoqInt.neg_one, sbnd, sm1, sm2) (CoqInt.one, sbnd, sm1, sm2)
        l1 l2
        (CoqInt.zero, sbnd, sm1, sm2)
         in 
    (lex_comp i1 i2, bnd, bv1, bv2)
  | Por p1 q1, Por p2 q2 =>
    let '(i1, bnd1, bv1, bv2) := pat_compare state p1 p2 in
    if negb (CoqInt.is_zero  i1) then (i1, bnd1, bv1, bv2)
    else 
      let i2 := or_cmp bv1 bv1 q1 q2 in
      (i2, bnd1, bv1, bv2)
  | Pas p1 v1, Pas p2 v2 =>
    let '(i1, bnd, bv1, bv2) := pat_compare state p1 p2 in
    (i1, CoqBigInt.succ bnd, Mvs.add v1 bnd bv1, Mvs.add v2 bnd bv2)
  | Pwild, _  => (CoqInt.neg_one, bnd, bv1, bv2) | _, Pwild  => (CoqInt.one, bnd, bv1, bv2)
  | Pvar _, _ => (CoqInt.neg_one, bnd, bv1, bv2) | _, Pvar _ => (CoqInt.one, bnd, bv1, bv2)
  | Papp _ _, _ => (CoqInt.neg_one, bnd, bv1, bv2) | _, Papp _ _ => (CoqInt.one, bnd, bv1, bv2)
  | Por _ _, _  => (CoqInt.neg_one, bnd, bv1, bv2) | _, Por _ _  => (CoqInt.one, bnd, bv1, bv2)
  end.

(*TODO move*)
Definition list_compare {A B: Type} (cmp: A -> B -> CoqInt.int) (l1: list A) (l2: list B) : CoqInt.int :=
  fold_left2_def (fun acc x1 x2 => lex_comp acc (cmp x1 x2))
    CoqInt.neg_one CoqInt.one l1 l2 CoqInt.zero. 

Fixpoint t_compare_aux (bnd: CoqBigInt.t) (vml1 vml2: Mvs.t CoqBigInt.t)
  (t1 t2: term_c) : CoqInt.int :=
  (*No shortcuts - TODO ocaml*)
  let i1 := oty_compare (t_ty_of t1) (t_ty_of t2) in
  lex_comp i1 (
  let i2 := if attr then (Sattr.compare (t_attrs_of t1) (t_attrs_of t2)) else CoqInt.zero in
  lex_comp i2 (
  let i3 := if loc then option_compare LocTy.compare (t_loc_of t1) (t_loc_of t2) else CoqInt.zero in
  lex_comp i3 (
    match (t_node_of t1), (t_node_of t2) with
      | Tvar v1, Tvar v2 =>
        var_compare vml1 vml2 v1 v2
      | Tconst c1, Tconst c2 =>
        ConstantDefs.compare_const_aux const c1 c2
      | Tapp s1 l1, Tapp s2 l2 =>
        let i1 := ls_compare s1 s2 in
        lex_comp i1 (
          fold_left2_def (fun acc t1 t2 =>
            lex_comp acc (t_compare_aux bnd vml1 vml2 t1 t2))
          CoqInt.neg_one CoqInt.one l1 l2 CoqInt.zero)
      | Tif f1 t1 e1, Tif f2 t2 e2 =>
        let i1 := t_compare_aux bnd vml1 vml2 f1 f2 in
        lex_comp i1 (
        let i2 := t_compare_aux bnd vml1 vml2 t1 t2 in
        lex_comp i2 (
        t_compare_aux bnd vml1 vml2 e1 e2))
      | Tlet t1 (v1, b1, e1), Tlet t2 (v2, b2, e2) =>
        let i1 := t_compare_aux bnd vml1 vml2 t1 t2 in
        lex_comp i1 (
        let vml1 := Mvs.add v1 bnd vml1 in
        let vml2 := Mvs.add v2 bnd vml2 in
        t_compare_aux (CoqBigInt.succ bnd) vml1 vml2 e1 e2)
      | Tcase t1 bl1, Tcase t2 bl2 =>
        let i1 := t_compare_aux bnd vml1 vml2 t1 t2 in
        lex_comp i1 (
        let b_compare x1 x2 :=
          let '(p1, b1, t1) := x1 in 
          let '(p2, b2, t2) := x2 in
          let '(ip, bnd, bv1, bv2) := pat_compare (bnd, Mvs.empty, Mvs.empty) p1 p2 in
          lex_comp ip (
            let vml1 := Mvs.union _ (fun x n1 n2 => Some n1) bv1 vml1 in
            let vml2 := Mvs.union _ (fun x n1 n2 => Some n1) bv2 vml2 in
            t_compare_aux bnd vml1 vml2 t1 t2
          ) in
        list_compare b_compare bl1 bl2)
      | Teps (v1, b1, e1), Teps (v2, b2, e2) => 
        let vml1 := Mvs.add v1 bnd vml1 in
        let vml2 := Mvs.add v2 bnd vml2 in
        t_compare_aux (CoqBigInt.succ bnd) vml1 vml2 e1 e2
      | Tquant q1 (vl1, b1, tr1, f1), Tquant q2 (vl2, b2, tr2, f2) =>
        let i1 := quant_compare q1 q2 in
        lex_comp i1 (
          let add bnd bv1 bv2 vl1 vl2 :=
            (*Don't need fold_left_def here because recurse on vsym lists
              but nicer to write this way*)
            fold_left2_def (fun acc v1 v2 =>
              let '(val, bnd, bv1, bv2) := acc in
              (*val is so that different lengths compare differently*)
              (val, CoqBigInt.succ bnd, Mvs.add v1 bnd bv1, Mvs.add v2 bnd bv2))
              (CoqInt.neg_one, bnd, bv1, bv2)
              (CoqInt.one, bnd, bv1, bv2)
              vl1 vl2 (CoqInt.zero, bnd, bv1, bv2) in
          let '(i1, bnd, bv1, bv2) := add bnd Mvs.empty Mvs.empty vl1 vl2 in
          lex_comp i1 (
          (*Keep the first (quantified) var*)
          let vml1 := Mvs.union _ (fun x n1 n2 => Some n1) bv1 vml1 in
          let vml2 := Mvs.union _ (fun x n1 n2 => Some n1) bv2 vml2 in
          let tr_cmp t1 t2 := t_compare_aux bnd vml1 vml2 t1 t2 in
          let i2 := if trigger then list_compare (list_compare tr_cmp) tr1 tr2 else CoqInt.zero in
          lex_comp i2 (t_compare_aux bnd vml1 vml2 f1 f2)))
      | Tbinop op1 f1 g1, Tbinop op2 f2 g2 =>
          let i1 := binop_compare op1 op2 in
          lex_comp i1 (
          let i2 := t_compare_aux bnd vml1 vml2 g1 g2 in
          lex_comp i2 (
          t_compare_aux bnd vml1 vml2 f1 f2))
      | Tnot f1, Tnot f2 =>
          t_compare_aux bnd vml1 vml2 f1 f2
      | Ttrue, Ttrue => CoqInt.zero
      | Tfalse, Tfalse => CoqInt.zero
      | Tvar _, _   => CoqInt.neg_one | _, Tvar _   => CoqInt.one
      | Tconst _, _ => CoqInt.neg_one | _, Tconst _ => CoqInt.one
      | Tapp _ _, _   => CoqInt.neg_one | _, Tapp _ _   => CoqInt.one
      | Tif _ _ _, _    => CoqInt.neg_one | _, Tif _ _ _    => CoqInt.one
      | Tlet _ _, _   => CoqInt.neg_one | _, Tlet _ _   => CoqInt.one
      | Tcase _ _, _  => CoqInt.neg_one | _, Tcase _ _  => CoqInt.one
      | Teps _, _   => CoqInt.neg_one | _, Teps _   => CoqInt.one
      | Tquant _ _, _ => CoqInt.neg_one | _, Tquant _ _ => CoqInt.one
      | Tbinop _ _ _, _ => CoqInt.neg_one | _, Tbinop _ _ _ => CoqInt.one
      | Tnot _, _   => CoqInt.neg_one | _, Tnot _   => CoqInt.one
      | Ttrue, _    => CoqInt.neg_one | _, Ttrue    => CoqInt.one
    end))).

Definition t_compare_full t1 t2 := t_compare_aux CoqBigInt.zero Mvs.empty Mvs.empty t1 t2.

End TCompare.
