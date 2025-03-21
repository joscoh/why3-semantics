Require Import IntFuncs Monads (*TyDefs TermDefs TyFuncs IdentDefs ConstantDefs*).
Require Export TermDefs.
Require NumberFuncs.
Import MonadNotations.
Local Open Scope err_scope.

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
  s <- Svs.add_new (DuplicateVar v) v (pat_vars_of p) ;;
  err_ret (mk_pattern (Pas p v) s v.(vs_ty)).

Definition pat_or_aux (p q: pattern_c) : errorM pattern_c :=
  if Svs.equal (pat_vars_of p) (pat_vars_of q) then
    err_ret (mk_pattern (Por p q) (pat_vars_of p) (pat_ty_of p))
  else
    let s := Mvs.union _ (fun _ _ _ => None) (pat_vars_of p) (pat_vars_of q) in
    x <- Svs.choose s ;;
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
    s1 <- s ;;
    let dups := Mvs.inter (fun _ _ _ => Some tt) s1 (pat_vars_of p) in
    if negb (Mvs.is_empty _ dups) then
      x <- Mvs.choose _ dups ;;
      throw (DuplicateVar (fst x))
    else
    (*Compute union*)
    err_ret (Mvs.union _ (fun _ _ _ => None) s1 (pat_vars_of p))
  ) pl (err_ret Svs.empty) in

  s <- dups ;;
  err_ret (mk_pattern (Papp f pl) s t).

(* Generic Traversal Functions *)
Definition pat_map_aux (fn: pattern_c -> errorM pattern_c) (p: pattern_c) : errorM pattern_c :=
  match (pat_node_of p) with
  | Pwild => err_ret p
  | Pvar _ => err_ret p
  | Papp s pl =>
    l <- errorM_list (map fn pl) ;;
    pat_app_aux s l (pat_ty_of p)
  | Pas p v => 
    p1 <- fn p ;;
    pat_as_aux p1 v
  | Por p q => 
    p1 <- fn p ;;
    q1 <- fn q ;;
    pat_or_aux p1 q1
  end.

(*TODO: include monad?*)
Definition pat_map (fn: pattern_c -> pattern_c): pattern_c -> errorM pattern_c  :=
  pat_map_aux (fun p => 
    let res := fn p in
    _ <- ty_equal_check (pat_ty_of p) (pat_ty_of res) ;;
    err_ret res).

Definition pat_map_err (fn: pattern_c -> errorM pattern_c): pattern_c -> errorM pattern_c  :=
  pat_map_aux (fun p => 
    res <- fn p ;;
    _ <- ty_equal_check (pat_ty_of p) (pat_ty_of res) ;;
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

(*We need to do all of this because we include the types in
  everything, so we check for consistency*)
(*This gets ugly with the state (from ty_match)*)
Definition pat_app (fs: lsymbol) (pl: list pattern_c) (t: ty_c) : 
  errorHashconsT _ pattern_c :=
  (*First, make sure that the result types are matchable
    (i.e. list int vs list a maps a to int)*)
  (s <- (match fs.(ls_value) with
            | Some vty => ty_match Mtv.empty vty t
            | None => errst_lift2 (throw (FunctionSymbolExpected fs))
  end) ;;
  let mtch s ty p := ty_match s ty (pat_ty_of p) in
  o <- fold_left2_errst mtch s fs.(ls_args) pl ;;
  errst_lift2 (match o with
  | None => throw (BadArity (fs, int_length pl))
  | Some _ => if CoqBigInt.is_zero fs.(ls_constr) then throw (ConstructorExpected fs)
  else pat_app_aux fs pl t
  end))%errst 
  .

Definition pat_as (p: pattern_c) (v: vsymbol) : errorM pattern_c :=
  _ <- ty_equal_check (pat_ty_of p) v.(vs_ty) ;;
  pat_as_aux p v.

Definition pat_or (p q: pattern_c) : errorM pattern_c :=
  _ <- ty_equal_check (pat_ty_of p) (pat_ty_of q) ;;
  pat_or_aux p q.

(*NOTE: Why3 uses the (type-safe) pat_map function to implement
  the [pat_rename_all] function.
  This checks for the same variables in an "or" pattern, etc.
  But we will only be using this with fresh (and well-typed) variables
  applied consistently, and this function is not callable
  outside of the module.
  So we will use an unsafe map function, which avoids
  putting everything (including term substitution) into
  an error monad
  TODO: make sure this is safe*)

Definition pat_app_unsafe (f: lsymbol) (pl: list pattern_c) (t: ty_c) :
  pattern_c :=
  (*Create union of all elements*)
  let un : Svs.t := fold_left (fun (s: Svs.t) p =>
    Svs.union s (pat_vars_of p)) pl Svs.empty in
  mk_pattern (Papp f pl) un t.

Definition pat_as_unsafe (p: pattern_c) (v: vsymbol) : pattern_c :=
  let s := Svs.add v (pat_vars_of p) in
  mk_pattern (Pas p v) s v.(vs_ty).

Definition pat_or_unsafe (p q: pattern_c) : pattern_c :=
  mk_pattern (Por p q) (pat_vars_of p) (pat_ty_of p).

Definition pat_map_unsafe (fn: pattern_c -> pattern_c) (p: pattern_c) : pattern_c :=
  match (pat_node_of p) with
  | Pwild | Pvar _ => p
  | Papp s pl => pat_app_unsafe s (map fn pl) (pat_ty_of p)
  | Pas p v => pat_as_unsafe (fn p) v
  | Por p q => pat_or_unsafe (fn p) (fn q)
  end.

(*Rename all variables in a pattern*)
Fixpoint pat_rename_all (m: Mvs.t vsymbol) (p: pattern_c) : pattern_c:=
  match (pat_node_of p) with
  | Pvar v => 
    match Mvs.find_opt v m with
    | Some v1 => (pat_var v1)
    | None => p (*NOTE: should never occur*)
    end
  | Pas p v =>
    let p1 := pat_rename_all m p in
    pat_as_unsafe p1
    match Mvs.find_opt v m with
      | Some v1 => v1
      | None => v (*Should never occur*)
      end
  | _ => pat_map_unsafe (pat_rename_all m) p
  end.


(*Term equality modulo alpha-equivalence and location*)
Section TCompare.
Variable trigger attr loc const: bool.

Definition list_comp l : CoqInt.int :=
  fold_left lex_comp l CoqInt.zero.

(*Compare variables v1 and v2.
  To be equal, they must either be mapped to each other in each map
  or not in either map and equal*)
Definition var_compare (m1 m2: Mvs.t CoqBigInt.t) (v1 v2: vsymbol) : CoqInt.int :=
  match Mvs.find_opt v1 m1, Mvs.find_opt v2 m2 with
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
    

Definition or_cmp_vsym (bv1 bv2: Mvs.t CoqBigInt.t) (v1 v2: vsymbol) :=
  match Mvs.find_opt v1 bv1, Mvs.find_opt v2 bv2 with
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

(*Using only structural/decidable equality is slow*)
Definition t_similar (t1 t2: term_c) : bool :=
  oty_equal (t_ty_of t1) (t_ty_of t2) &&
  match (t_node_of t1), (t_node_of t2) with
  | Tvar v1, Tvar v2 => vs_equal v1 v2
  | Tconst c1, Tconst c2 => CoqInt.int_eqb 
    (ConstantDefs.compare_const_aux true c1 c2) CoqInt.zero
  | Tapp s1 l1, Tapp s2 l2 => ls_equal s1 s2 && 
    list_eqb term_eqb_fast l1 l2
  | Tif f1 t1 e1, Tif f2 t2 e2 => term_eqb_fast f1 f2 && term_eqb_fast t1 t2 
    && term_eqb_fast e1 e2
  | Tlet t1 bv1, Tlet t2 bv2 => term_eqb_fast t1 t2 && 
    term_bound_eqb_fast bv1 bv2
  | Tcase t1 bl1, Tcase t2 bl2 => term_eqb_fast t1 t2 &&
    list_eqb term_branch_eqb_fast bl1 bl2
  | Teps bv1, Teps bv2 => term_bound_eqb_fast bv1 bv2
  | Tquant q1 bv1, Tquant q2 bv2 => 
    quant_eqb q1 q2 && term_quant_eqb_fast bv1 bv2
  | Tbinop o1 f1 g1, Tbinop o2 f2 g2 =>
    binop_eqb o1 o2 && term_eqb_fast f1 f2 && term_eqb_fast g1 g2
  | Tnot f1, Tnot f2 => term_eqb_fast f1 f2
  | Ttrue, Ttrue => true
  | Tfalse, Tfalse => true
  | _, _ => false
  end.

(*Hashing*)

Fixpoint or_hash bv (q: pattern_c) : CoqBigInt.t :=
  match (pat_node_of q) with
  | Pwild => CoqBigInt.zero
  | Pvar v => CoqBigInt.succ match Mvs.find_opt v bv with
              | Some i => i
              (*Should never occur by typing*)
              | None => CoqBigInt.zero
              end
  | Papp s l => hashcons.combine_big_list (or_hash bv) (ls_hash s) l
  | Por p q => hashcons.combine_big (or_hash bv p) (or_hash bv q)
  | Pas p v => let j := match Mvs.find_opt v bv with
              | Some i => i
              (*Should never occur*)
              | None => CoqBigInt.zero
              end in 
              hashcons.combine_big (or_hash bv p) (CoqBigInt.succ j)
  end.

(*Gives number of bound vars, updated map, hash value*)
Fixpoint pat_hash (bnd: CoqBigInt.t) (bv: Mvs.t CoqBigInt.t) (p: pattern_c) : 
  CoqBigInt.t * Mvs.t CoqBigInt.t * CoqBigInt.t :=
  match (pat_node_of p) with
  | Pwild => (bnd, bv, CoqBigInt.zero)
  | Pvar v => (CoqBigInt.succ bnd, Mvs.add v bnd bv, CoqBigInt.succ bnd)
  | Papp s l => 
    (*TODO: nested version of fold_left*)
    fold_left (fun acc p =>
      let '(bnd, bv, h) := acc in
      let '(bnd1, bv1, hp) := pat_hash bnd bv p in
      (bnd1, bv1, hashcons.combine_big h hp)) l (bnd, bv, ls_hash s)
  | Por p q =>
    let '(bnd1, bv1, hp) := pat_hash bnd bv p in
    (bnd1, bv1, hashcons.combine_big hp (or_hash bv1 q))
  | Pas p v =>
    let '(bnd1, bv1, hp) := pat_hash bnd bv p in
    (CoqBigInt.succ bnd1, Mvs.add v bnd bv, hashcons.combine_big hp (CoqBigInt.succ bnd1))
  end.

Section TermHash.

Variable (trigger attr const : bool).

(*For now, set to small (and unique) primes*)

Definition q_hash (q: quant) : CoqBigInt.t :=
  match q with
  | Tforall => CoqBigInt.five
  | Texists => CoqBigInt.seven
  end.

Definition binop_hash (b: binop) : CoqBigInt.t :=
  match b with
  | Tand => CoqBigInt.eleven
  | Tor => CoqBigInt.thirteen
  | Timplies => CoqBigInt.seventeen
  | Tiff => CoqBigInt.nineteen
  end.

Fixpoint t_hash_aux (bnd: CoqBigInt.t) (vml: Mvs.t CoqBigInt.t) (t: term_c) : CoqBigInt.t :=
  let h := oty_hash (t_ty_of t) in
  let h1 := if attr then Sattr.fold (fun l h => hashcons.combine_big (attr_hash l) h) (t_attrs_of t) h else h in
  hashcons.combine_big h1 (
    match (t_node_of t) with
    | Tvar v => match Mvs.find_opt v vml with
                | Some i => CoqBigInt.succ i
                | None => vs_hash v
                end
    | Tconst c =>
      if const then constant_hash c else
      match c with
      | ConstInt i => i.(NumberDefs.il_int)
      | ConstReal r => NumberDefs.real_value_hash r.(NumberDefs.rl_real)
      | ConstStr c => ConstantDefs.str_hash c
      end
    | Tapp s l => hashcons.combine_big_list (t_hash_aux bnd vml) (ls_hash s) l
    | Tif f t e =>
      hashcons.combine2_big (t_hash_aux bnd vml f) (t_hash_aux bnd vml t) (t_hash_aux bnd vml e)
    | Tlet t (v, b, e) =>
      hashcons.combine_big (t_hash_aux bnd vml t)
        (t_hash_aux (CoqBigInt.succ bnd) (Mvs.add v bnd vml) e)
    | Tcase t bl =>
      let h1 := t_hash_aux bnd vml t in
      let b_hash x :=
        let '(p, b, t) := x in
        let '(bnd, bv, hp) := pat_hash bnd Mvs.empty p in
        (*Overwrite with newest bound value*)
        let vml := Mvs.union _ (fun x n1 n2 => Some n1) bv vml in
        hashcons.combine_big hp (t_hash_aux bnd vml t) in
      hashcons.combine_big_list b_hash h bl
    | Teps (v, b, e) =>
      t_hash_aux (CoqBigInt.succ bnd) (Mvs.add v bnd vml) e
    | Tquant q (vl, b, tr, f) =>
      let h := q_hash q in
      let '(bnd, bv) := fold_left (fun acc v => 
        let '(bnd, bv) := acc in
        (CoqBigInt.succ bnd, Mvs.add v bnd bv)) vl (bnd, Mvs.empty) in
      let vml := Mvs.union _ (fun x n1 n2 => Some n1) bv vml in
      let h :=
        if trigger then fold_left (hashcons.combine_big_list (t_hash_aux bnd vml)) tr h
        else h in
      hashcons.combine_big h (t_hash_aux bnd vml f)
    | Tbinop op f g =>
      hashcons.combine2_big (binop_hash op) (t_hash_aux bnd vml f) (t_hash_aux bnd vml g)
    | Tnot f => hashcons.combine_big CoqBigInt.one (t_hash_aux bnd vml f)
    | Ttrue => CoqBigInt.two
    | Tfalse => CoqBigInt.three
    end
  ).

Definition t_hash_full t := t_hash_aux CoqBigInt.zero Mvs.empty t.

End TermHash.


(*Derived versions*)
Definition t_hash_strict (t: term_c) : CoqBigInt.t :=
  t_hash_full true true true t.
Definition t_equal_strict (t1 t2: term_c) : bool :=
  CoqInt.int_eqb (t_compare_full true true true true t1 t2) (CoqInt.zero).
Definition t_compare_strict (t1 t2: term_c) : CoqInt.int :=
  t_compare_full true true true true t1 t2.
(*TODO: skip sets and maps for now, see if we need them
  (but hopefully not because hashing is not injective)*)

Definition t_hash (t: term_c) : CoqBigInt.t :=
  t_hash_full false false false t.
Definition t_equal (t1 t2: term_c) : bool :=
  CoqInt.int_eqb (t_compare_full false false false false t1 t2) (CoqInt.zero).
Definition t_compare (t1 t2: term_c) : CoqInt.int :=
  t_compare_full false false false false t1 t2.

(* Type Checking *)
Definition TermExpected (t: term_c) : errtype :=
  mk_errtype "TermExpected" t.
Definition FmlaExpected (t: term_c) : errtype :=
  mk_errtype "FmlaExpected" t.

Definition t_type (t: term_c) : errorM ty_c :=
  match (t_ty_of t) with
  | Some ty => err_ret ty
  | None => throw (TermExpected t)
  end.

Definition t_prop (f: term_c) : errorM term_c :=
  if negb (isSome (t_ty_of f)) then err_ret f else
    throw (FmlaExpected f).

Definition t_ty_check (t: term_c) (typ: option ty_c) : errorM unit :=
  match typ, (t_ty_of t) with
  | Some l, Some r => ty_equal_check l r
  | Some _, None => throw (TermExpected t)
  | None, Some _ => throw (FmlaExpected t)
  | None, None => err_ret tt
  end.

Definition vs_check (v: vsymbol) (t: term_c) : errorM unit :=
  typ <- t_type t;;
  ty_equal_check v.(vs_ty) typ.

(*Trigger Equality and Traversal*)
Definition tr_equal := list_eqb (list_eqb t_equal).

Definition tr_map {A B: Type} (fn: A -> B) :=
  map (map fn).

Definition tr_fold {A B: Type} (fn: A -> B -> A) (acc: A) (l: list (list B)) 
  := fold_left (fun acc tms => fold_left (fun acc t => fn acc t) tms acc) l acc. 

Definition tr_map_fold {A B C: Type} (fn: A -> B -> A * C) :=
  map_fold_left (map_fold_left fn).

(* Hash-consing for terms and formulas*)

Definition vars_union (s1 s2: Mvs.t CoqBigInt.t) : Mvs.t CoqBigInt.t :=
  Mvs.union _ (fun _ m n => Some (CoqBigInt.add m n)) s1 s2.

Definition add_b_vars {A B: Type} (s: Mvs.t CoqBigInt.t) (x: A * bind_info * B) : Mvs.t CoqBigInt.t :=
  let '(_, b, _) := x in
  vars_union s b.(bv_vars).

Fixpoint t_vars (t: term_c) : Mvs.t CoqBigInt.t :=
  match (t_node_of t) with
  | Tvar v => Mvs.singleton _ v CoqBigInt.one
  | Tconst _ => Mvs.empty
  | Tapp _ tl => fold_left (fun s x => vars_union s (t_vars x)) tl Mvs.empty
  | Tif f t e => vars_union (vars_union (t_vars f) (t_vars t)) (t_vars e)
  | Tlet t bt => add_b_vars (t_vars t) bt
  | Tcase t bl => List.fold_left add_b_vars bl (t_vars t)
  | Teps (_, b, _) => b.(bv_vars)
  | Tquant _ (_, b, _, _) => b.(bv_vars)
  | Tbinop _ f1 f2 => vars_union (t_vars f1) (t_vars f2)
  | Tnot f => t_vars f
  | Ttrue | Tfalse => Mvs.empty
  end.

(*Avoid mutual recursion*)
Definition add_t_vars s t := vars_union s (t_vars t).

(*Skip add_nt_vars, not used*)

(*Hash-Consing Constructors for Terms*)
(*NOTE: not actually hash consing*)

Definition mk_term (n: term_node) (t: option ty_c) : term_c :=
  mk_term_c n t (Sattr.empty) None.

Definition t_var v := mk_term (Tvar v) (Some v.(vs_ty)).
Definition t_const1 c t := mk_term (Tconst c) (Some t).
Definition t_app1 f tl t := mk_term (Tapp f tl) t.
Definition t_if1 f t1 t2 := mk_term (Tif f t1 t2) (t_ty_of t2).
Definition t_let1 t1 bt t := mk_term (Tlet t1 bt) t.
Definition t_case1 t1 bl t := mk_term (Tcase t1 bl) t.
Definition t_eps1 bf t := mk_term (Teps bf) t.
Definition t_quant1 q qf := mk_term (Tquant q qf) None.
Definition t_binary1 op f g := mk_term (Tbinop op f g) None.
Definition t_not1 f := mk_term (Tnot f) None.
Definition t_true := mk_term Ttrue None.
Definition t_false := mk_term Tfalse None.

Definition t_attr_set1 (loc: option LocTy.position) (l: Sattr.t) (t: term_c) : term_c :=
  mk_term_c (t_node_of t) (t_ty_of t) l loc.

Definition t_attr_add (l: attribute) (t: term_c) : term_c :=
  mk_term_c (t_node_of t) (t_ty_of t) (Sattr.add l (t_attrs_of t)) (t_loc_of t).

Definition t_attr_remove (l: attribute) (t: term_c) : term_c :=
  mk_term_c (t_node_of t) (t_ty_of t) (Sattr.remove l (t_attrs_of t)) (t_loc_of t).

(*A little hack: all we need (for now) is to remove attributes, so
  we will remove all with name. So we can ignore hashcons*)
Definition t_attr_remove_name (s: string) (t: term_c) : term_c :=
  mk_term_c (t_node_of t) (t_ty_of t) 
    (Sattr.filter (fun a => negb (String.eqb a.(attr_string) s)) (t_attrs_of t))
    (t_loc_of t).


Definition t_attr_copy (s t: term_c) : term_c :=
  (*No reference equality check*)
  if t_similar s t && Sattr.is_empty (t_attrs_of t) && negb (isSome (t_loc_of t)) then s else
  let attrs := Sattr.union (t_attrs_of s) (t_attrs_of t) in
  let loc := if isNone (t_loc_of t) then (t_loc_of s) else (t_loc_of t) in
  mk_term_c (t_node_of t) (t_ty_of t) attrs loc.

(* Unsafe Map*)

Local Open Scope state_scope.

Definition bound_map {A B C D: Type} (f: A -> B) (x: C * D * A) : C * D * B :=
  match x with
  | (u, b, e) => (u, b, f e)
  end.

Definition t_map_unsafe (fn: term_c -> term_c) (t: term_c) : term_c :=
  t_attr_copy t (match (t_node_of t) with
  | Tvar _ | Tconst _ => t
  | Tapp f tl => t_app1 f (map fn tl) (t_ty_of t)
  | Tif f t1 t2 => t_if1 (fn f) (fn t1) (fn t2)
  | Tlet e b => t_let1 (fn e) (bound_map fn b) (t_ty_of t)
  | Tcase e bl => t_case1 (fn e) (map (bound_map fn) bl) (t_ty_of t)
  | Teps b => t_eps1 (bound_map fn b) (t_ty_of t)
  | Tquant q (vl, b, tl, f) => t_quant1 q (vl, b, tr_map fn tl, fn f)
  | Tbinop op f1 f2 => t_binary1 op (fn f1) (fn f2)
  | Tnot f1 => t_not1 (fn f1)
  | Ttrue | Tfalse => t
  end).

(*error*)
Local Open Scope errst_scope.

(*NOTE: would be really nice to generalize to monads*)
Definition bound_map_errst {St A B C D: Type} (f: A -> errState St B) (x: C * D * A) : errState St (C * D * B) :=
  match x with
  | (u, b, e) => 
    e1 <- f e;;
    errst_ret (u, b, e1)
  end.

(*Get state out of trigger map*)
Definition errst_tr {St A: Type} (l: list (list (errState St A))) : errState St (list (list A)) :=
  errst_list (map (fun l => errst_list l) l).

Definition tr_map_errst  {St: Type} (fn: term_c -> errState St term_c) (tl : list (list term_c)) := 
  errst_tr (tr_map fn tl).

Definition t_map_errst_unsafe {St: Type} (fn: term_c -> errState St term_c) (t: term_c) : errState St term_c :=
  t1 <- (match (t_node_of t) with
  | Tvar _ | Tconst _ => errst_ret t
  | Tapp f tl =>
    l <- errst_list (map fn tl) ;;
    errst_ret (t_app1 f l (t_ty_of t))
  | Tif f t1 t2 =>
    f1 <- fn f ;;
    t1' <- fn t1 ;;
    t2' <- fn t2 ;;
    errst_ret (t_if1 f1 t1' t2')
  | Tlet e b =>
    e1 <- fn e ;;
    b1 <- (bound_map_errst fn b);;
    errst_ret (t_let1 e1 b1 (t_ty_of t))
  | Tcase e bl => 
    e1 <- fn e;;
    l <- (errst_list (map (bound_map_errst fn) bl));;
    errst_ret (t_case1 e1 l (t_ty_of t))
  | Teps b => 
    b1 <- bound_map_errst fn b ;;
    errst_ret (t_eps1 b1 (t_ty_of t))
  | Tquant q (vl, b, tl, f) => 
    l <- tr_map_errst fn tl ;;
    f1 <- fn f;;
    errst_ret (t_quant1 q (vl, b, l, f1))
  | Tbinop op f1 f2 => 
    f1' <- fn f1;;
    f2' <- fn f2;;
    errst_ret (t_binary1 op f1' f2')
  | Tnot f1 => 
    f1' <- fn f1;;
    errst_ret (t_not1 f1')
  | Ttrue | Tfalse => errst_ret t
  end) ;;
  
  errst_ret (t_attr_copy t t1).

Local Open Scope state_scope.

Definition bound_map_ctr {A B C D: Type} (f: A -> ctr B) (x: C * D * A) : ctr (C * D * B) :=
  match x with
  | (u, b, e) => 
    e1 <- f e;;
    st_ret (u, b, e1)
  end.

(*Get state out of trigger map*)
(*TODO: generalize to all state?*)
Definition st_tr {A: Type} (l: list (list (ctr A))) : ctr (list (list A)) :=
  st_list (map (fun l => st_list l) l).


Definition t_map_ctr_unsafe (fn: term_c -> ctr term_c) (t: term_c) : ctr term_c :=
  t1 <- (match (t_node_of t) with
  | Tvar _ | Tconst _ => st_ret t
  | Tapp f tl =>
    l <- st_list (map fn tl) ;;
   st_ret (t_app1 f l (t_ty_of t))
  | Tif f t1 t2 =>
    f1 <- fn f ;;
    t1' <- fn t1 ;;
    t2' <- fn t2 ;;
    st_ret (t_if1 f1 t1' t2')
  | Tlet e b =>
    e1 <- fn e ;;
    b1 <- (bound_map_ctr fn b);;
    st_ret (t_let1 e1 b1 (t_ty_of t))
  | Tcase e bl => 
    e1 <- fn e;;
    l <- (st_list (map (bound_map_ctr fn) bl));;
    st_ret (t_case1 e1 l (t_ty_of t))
  | Teps b => 
    b1 <- bound_map_ctr fn b ;;
    st_ret (t_eps1 b1 (t_ty_of t))
  | Tquant q (vl, b, tl, f) => 
    l <- st_tr (tr_map fn tl) ;;
    f1 <- fn f;;
    st_ret (t_quant1 q (vl, b, l, f1))
  | Tbinop op f1 f2 => 
    f1' <- fn f1;;
    f2' <- fn f2;;
    st_ret (t_binary1 op f1' f2')
  | Tnot f1 => 
    f1' <- fn f1;;
    st_ret (t_not1 f1')
  | Ttrue | Tfalse => st_ret t
  end) ;;
  
  st_ret (t_attr_copy t t1).

(*Unsafe Fold*)

Definition bound_fold {A B C D E: Type} (fn : A -> B -> C) (acc : A)
  (x: D * E * B) : C := 
  match x with
  | (_, _, e) => fn acc e
  end.

Definition t_fold_unsafe {A: Type} (fn: A -> term_c -> A) (acc: A) (t: term_c) : A :=
  match t_node_of t with
  | Tvar _ | Tconst _ => acc
  | Tapp _ tl => fold_left fn tl acc
  | Tif f t1 t2 => fn (fn (fn acc f) t1) t2
  | Tlet e b => fn (bound_fold fn acc b) e
  | Tcase e bl => fold_left (bound_fold fn) bl (fn acc e)
  | Teps b => bound_fold fn acc b
  | Tquant _ (_, b, tl, f1) => fn (tr_fold fn acc tl) f1
  | Tbinop _ f1 f2 => fn (fn acc f1) f2
  | Tnot f1 => fn acc f1
  | Ttrue | Tfalse => acc
  end.

(* Unsafe Map_fold *)

Definition bound_map_fold {A B C D E F: Type} (fn: A -> B -> C * D)
  (acc: A) (x : E * F * B) : C * (E * F * D) :=
  match x with
  | (u, b, e) => let '(acc, e) := fn acc e in
    (acc, (u, b, e))
  end.

Definition t_map_fold_unsafe {A: Type} (fn : A -> term_c -> A * term_c)
  (acc: A) (t: term_c) : (A * term_c) :=
  match (t_node_of t) with
  | Tvar _ | Tconst _ => (acc, t)
  | Tapp f tl =>
    let '(acc, sl) := map_fold_left fn acc tl in
    (acc, t_attr_copy t (t_app1 f sl (t_ty_of t)))
  | Tif f t1 t2 =>
    let '(acc, g) := fn acc f in
    let '(acc, s1) := fn acc t1 in
    let '(acc, s2) := fn acc t2 in
    (acc, t_attr_copy t (t_if1 g s1 s2))
  | Tlet e b =>
      let '(acc, e) := fn acc e in
      let '(acc, b) := bound_map_fold fn acc b in
      (acc, t_attr_copy t (t_let1 e b (t_ty_of t)))
  | Tcase e bl =>
      let '(acc, e) := fn acc e in
      let '(acc, bl) := map_fold_left (bound_map_fold fn) acc bl in
      (acc, t_attr_copy t (t_case1 e bl (t_ty_of t)))
  | Teps b =>
      let '(acc, b) := bound_map_fold fn acc b in
      (acc, t_attr_copy t (t_eps1 b (t_ty_of t)))
  | Tquant q (vl, b, tl, f1) =>
      let '(acc, tl) := tr_map_fold fn acc tl in
      let '(acc, f1) := fn acc f1 in
      (acc, t_attr_copy t (t_quant1 q (vl, b, tl, f1)))
  | Tbinop op f1 f2 =>
      let '(acc, g1) := fn acc f1 in
      let '(acc, g2) := fn acc f2 in
      (acc, t_attr_copy t (t_binary1 op g1 g2))
  | Tnot f1 =>
      let '(acc, g1) := fn acc f1 in
      (acc, t_attr_copy t (t_not1 g1))
  | Ttrue | Tfalse => (acc, t)
  end.

(*Type-unsafe term substitution*)

(*Note: this is eager, not lazy, unlike the current
  Why3 implementation*)
Definition fresh_vsymbol (v: vsymbol) : ctr vsymbol :=
  create_vsymbol (id_clone1 None Sattr.empty v.(vs_name)) v.(vs_ty).

Definition vs_rename (h: Mvs.t term_c) (v: vsymbol) : 
  ctr (Mvs.t term_c * vsymbol) :=
  u <- fresh_vsymbol v;;
  st_ret (Mvs.add v (t_var u) h, u).

Definition bnd_new (s: Mvs.t CoqBigInt.t) : bind_info :=
  {| bv_vars := s|}.

Definition t_close_bound (v: vsymbol) (t: term_c) :
  vsymbol * bind_info * term_c :=
  (v, bnd_new (Mvs.remove _ v (t_vars t)), t).

(*Given a set of variables, generate new variables in a map.
  NOTE: this is not very efficient: nlogn (or so) vs O(n) for
  smart implementation. But the map interface does not accept a monad
  TODO: should we change this?*)
Fixpoint add_vars (l: list vsymbol) : ctr (Mvs.t vsymbol) :=
  match l with
  | nil => st_ret Mvs.empty
  | v :: vs => 
    v1 <- fresh_vsymbol v ;;
    m <- add_vars vs ;;
    st_ret (Mvs.add v v1 m)
  end.

Definition pat_rename (h: Mvs.t term_c) (p: pattern_c) :
  ctr (Mvs.t term_c * pattern_c) := 
  m <- add_vars (Svs.elements (pat_vars_of p)) ;;
  let p := pat_rename_all m p in
  (*Keep the newly-alpha-renamed ones (second) if overlap*)
  st_ret (Mvs.union _ (fun _ _ t => Some t) h (Mvs.map t_var m), p).

Definition t_close_branch (p: pattern_c) (t: term_c) : 
  (pattern_c * bind_info * term_c) :=
  (p, bnd_new (Mvs.set_diff _ _ (t_vars t) (pat_vars_of p)), t).

(*Once again, we will have an "unsafe" [t_close_quant], which
  does not check the type of the inputted term and which is only
  used internally, and a public function that is type-safe*)
Definition t_close_quant_unsafe (vl: list vsymbol) 
  (tl: list (list term_c)) (f: term_c) :
  list vsymbol * bind_info * list (list term_c) * term_c :=
  let del_v s v := Mvs.remove _ v s in
  let s := tr_fold add_t_vars (t_vars f) tl in
  let s := fold_left del_v vl s in
  (vl, bnd_new s, tl, f).

Definition t_close_quant (vl: list vsymbol) 
  (tl: list (list term_c)) (f: term_c) :
  errorM (list vsymbol * bind_info * list (list term_c) * term_c) :=
  let '(vl, s, tl, f) := t_close_quant_unsafe vl tl f in
  (p <- t_prop f ;;
  err_ret (vl, s, tl, p))%err.

(*TODO: they use map_fold_left, we need state*)
Fixpoint vl_rename_aux (vl: list vsymbol) 
  (acc: ctr (Mvs.t term_c * list vsymbol)) : ctr (Mvs.t term_c * list vsymbol) :=
  match vl with
  | nil => acc
  | v :: vs =>
    x <- acc;;
    let '(m, vls) := x in
    x1 <- vs_rename m v ;;
    let '(m1, v1) := x1 in
    vl_rename_aux vs (st_ret (m1, v1 :: vls))
  end.

Definition vl_rename (h: Mvs.t term_c) (vl: list vsymbol) :=
  x <- vl_rename_aux vl (st_ret (h, nil)) ;;
  st_ret (fst x, rev' (snd x)).

(* Fixpoint t_subst_unsafe_aux (m: Mvs.t term_c) (t: term_c) : ctr term_c :=
  let t_subst t := t_subst_unsafe_aux m t in

  let t_open_bnd {A: Type} (v : A) m t f : ctr (A * term_c) :=
    x <- f m v ;;
    let '(m, v) := x in
    t1 <- t_subst_unsafe_aux m t ;;
    st_ret (v, t1)
  in

  let t_open_quant vl m (tl : list (list term_c)) f :
    ctr (list vsymbol * list (list term_c) * term_c) :=
    x <- vl_rename m vl ;;
    let '(m, vl) := x in
    tl <- st_tr (tr_map (t_subst_unsafe_aux m) tl) ;;
    f1 <- t_subst_unsafe_aux m f;; 
    st_ret (vl, tl, f1)
  in

  let b_subst {A: Type} bv f (cl : A -> term_c -> (A * bind_info * term_c)) 
    : ctr (A * bind_info * term_c) :=
    let '(u, b, e) := bv in
    if Mvs.set_disjoint _ _ m b.(bv_vars) then st_ret bv else
    let m1 := Mvs.set_inter _ _ m b.(bv_vars) in
    y <- (fun v m t => t_open_bnd v m t f) u m1 e ;;
    let '(v, t1) := y in
    let x := cl v t1 in
    st_ret x in

  let b_subst1 bv : ctr (vsymbol * bind_info * term_c) :=
    b_subst bv vs_rename t_close_bound in

  let b_subst2 bv : ctr (pattern_c * bind_info * term_c) :=
    b_subst bv pat_rename t_close_branch in

  let b_subst3 bq :=
    let '(vl, b, tl, f1) := bq in
    if Mvs.set_disjoint _ _ m b.(bv_vars) then st_ret bq else
    let m1 := Mvs.set_inter _ _ m b.(bv_vars) in
    y <- t_open_quant vl m1 tl f1 ;;
    let '(vs, tr, t1) := y in
    let x := t_close_quant_unsafe vs tr t1 in
    st_ret x
  in

  
  match (t_node_of t) with
  | Tvar u => st_ret (t_attr_copy t (Mvs.find_def _ t u m))
  | Tlet e bt =>
    t1 <- t_subst e ;;
    b1 <- (b_subst1 bt) ;;
    st_ret (t_attr_copy t (t_let1 t1 b1 (t_ty_of t)))
  | Tcase e bl =>
    d <- t_subst e ;;
    bl <- st_list (map b_subst2 bl) ;;
    st_ret (t_attr_copy t (t_case1 d bl (t_ty_of t)))
  | Teps bf =>
    bf1 <- (b_subst1 bf);;
    st_ret (t_attr_copy t (t_eps1 bf1 (t_ty_of t)))
  | Tquant q bq =>
    bq1 <- b_subst3 bq ;;
    st_ret (t_attr_copy t (t_quant1 q bq1))
  | _ => t_map_ctr_unsafe t_subst t
  end. *)

Fixpoint t_subst_unsafe_aux (m: Mvs.t term_c) (t: term_c) : term_c :=
  match (t_node_of t) with
  | Tvar u => (t_attr_copy t (Mvs.find_def _ t u m))
  | Tlet e (v, b, t2) =>
    let e1 := (t_subst_unsafe_aux m e) in 
    (*Remove element of m corresponding to variable we substitute*)
    let m' := Mvs.remove _ v m in
    (*specialize to free vars of t2*)
    let m1 := Mvs.set_inter _ _ m' b.(bv_vars) in
    (*See if resulting is empty*)
    let e2 := if Mvs.is_empty _ m1 then t2 else t_subst_unsafe_aux m1 t2 in
    (*Create new [bind_info] *)
    let b1 := bnd_new (Mvs.remove _ v (t_vars e2) (*(b.(bv_vars))*)) in (*TODO: do this or compute from maps directly?*)
    t_attr_copy t (t_let1 e1 (v, b1, e2) (t_ty_of t))
  | Tcase e bl =>
    let e1 := (t_subst_unsafe_aux m e) in
    let bl2 := map
      (fun (x: pattern_c * bind_info * term_c) =>
        let m' := Mvs.set_diff _ _ m (pat_vars_of (fst (fst x))) in
        let m1 := Mvs.set_inter _ _ m' (snd (fst x)).(bv_vars) in
        let e2 := if Mvs.is_empty _ m1 then snd x else t_subst_unsafe_aux m1 (snd x) in
        let b1 := bnd_new (Mvs.set_diff _ _ (t_vars e2) (pat_vars_of (fst (fst x)))) in
        (fst (fst x), b1, e2)
        ) bl in
    t_attr_copy t (t_case1 e1 bl2 (t_ty_of t))
  | Teps (v, b, t1) =>
    let m' := Mvs.remove _ v m in
    let m1 := Mvs.set_inter _ _ m' b.(bv_vars) in
    let e2 := if Mvs.is_empty _ m1 then t1 else t_subst_unsafe_aux m1 t1 in
    let b1 := bnd_new (Mvs.remove _ v (t_vars e2)) in
    t_attr_copy t (t_eps1 (v, b1, e2) (t_ty_of t))
  | Tquant q (vs, b, tr, t1) =>
    let m' := Mvs.set_diff _ _ m (Svs.of_list vs) in
    let m1 := Mvs.set_inter _ _ m' b.(bv_vars) in
    let e2 := if Mvs.is_empty _ m1 then t1 else t_subst_unsafe_aux m1 t1 in
    let b1 := bnd_new (Mvs.set_diff _ _ (t_vars e2) (Svs.of_list vs)) in
    (*don't sub in triggers I think*)
    let tr2 := (tr_map (t_subst_unsafe_aux m) tr) in (*don't do optimization here*)
    t_attr_copy t (t_quant1 q (vs, b1, tr2, e2))
  | _ => t_map_unsafe (t_subst_unsafe_aux m) t
  end.

(* Definition t_subst_unsafe m t :=
  if Mvs.is_empty _ m then st_ret t else t_subst_unsafe_aux m t. *)

Definition t_subst_unsafe m t :=
  if Mvs.is_empty _ m then t else t_subst_unsafe_aux m t.

(* open bindings *)

(*The Why3 versions are stateful. For our purposes, stateless
  version suffice (and are much easier to prove/reason about).
  We will prove that we use them safely. We provide the
  stateful versions for API purposes: it causes problems in
  the test suite if we use stateless ones (in RAC)
  TODO: see why we have problem - we shouldn't*)

(*Need to define it this way instead of pattern matching
  so that Coq can tell it is recursive*)
Definition t_view_bound (x: term_bound) : vsymbol * term_c :=
  (fst (fst x), snd x).

Definition t_open_bound (x: term_bound) : ctr (vsymbol * term_c) :=
  let '(v, b, t) := x in
  y <- vs_rename Mvs.empty v ;;
  let '(m, v) := y in
  st_ret (v, (t_subst_unsafe m t)).

Definition t_view_branch (x: term_branch) : pattern_c * term_c :=
  (fst (fst x), snd x).

Definition t_open_branch (x: term_branch) : ctr (pattern_c * term_c) :=
  let '(p, b, t) := x in
  y <- pat_rename Mvs.empty p ;;
  let '(m, p) := y in
  st_ret (p, (t_subst_unsafe m t)).

(*Different because tuples in OCaml/Coq are different*)
(*TODO: figure out tuple things because this is annoying we don't
  want to duplicate everything - maybe just accept different tuples?*)
(*TODO: fix with tuple hack*)
Definition t_open_quant1 (x: term_quant) : ctr (list vsymbol * trigger * term_c) :=
  let '(vl, b, tl, f) := x in
  y <- vl_rename Mvs.empty vl ;;
  let '(m, vl) := y in
  st_ret (vl, (tr_map (t_subst_unsafe m) tl), (t_subst_unsafe m f)).

Definition t_view_quant (x: term_quant) : list vsymbol * trigger * term_c :=
  (fst (fst (fst x)), snd (fst x), snd x).

Definition t_open_bound_with (e: term_c) (x: term_bound) : errorM term_c :=
  (let '(v, b, t) := x in
  _ <- vs_check v e ;;
  let m := Mvs.singleton _ v e in
  err_ret (t_subst_unsafe m t))%err.

Definition t_view_quant_cb (fq: term_quant) : 
  list vsymbol * trigger * term_c *
  (list vsymbol -> trigger -> term_c -> errorM term_quant)  :=
  let '(vl, tl, f) := t_view_quant fq in
  let close vl' tl' f' :=
    if term_eqb_fast f f' &&
      list_eqb (list_eqb term_eqb_fast) tl tl' &&
      list_eqb vs_equal vl vl' 
    then err_ret fq else t_close_quant vl' tl' f'
  in
  (vl, tl, f, close).

(*skip t_clone_bound_id (for now)*)


(** open bindings with optimized closing callbacks *)
(*Josh - I think that these are so that you don't have to
  call t_close_bound (and calculuate vars, etc), you can just
  call the callback which, assuming you are just opening then
  closing, will just return the original tb*)
Definition t_open_bound_cb1 (tb : term_bound) : 
  ctr (vsymbol * term_c * (vsymbol -> term_c -> vsymbol * bind_info * term_c)) :=
  x <- t_open_bound tb ;;
  let '(v, t) := x in
  let close v' t' :=
    if term_eqb_fast t t' && vs_equal v v' then tb else
      t_close_bound v' t'
  in
  st_ret (v, t, close).

Definition t_open_branch_cb1 (tbr: term_branch) :=
  x <- t_open_branch tbr ;;
  let '(p, t) := x in
  let close p' t' :=
    if term_eqb_fast t t' && pattern_eqb_fast p p' then tbr else t_close_branch p' t'
  in
  st_ret (p, t, close).

(*This one is also in the error monad because of [t_close_quant]
  which checks the type of f'*)
Definition t_open_quant_cb1 (fq: term_quant) : ctr (list vsymbol * trigger * term_c *
  (list vsymbol -> trigger -> term_c -> errorM (list vsymbol * bind_info * trigger * term_c))) :=
  x <- (t_open_quant1 fq) ;;
  let '(vl, tl, f) := x in
  let close vl' tl' f' :=
    if term_eqb_fast f f' &&
      list_eqb (list_eqb term_eqb_fast) tl tl' &&
      list_eqb vs_equal vl vl'
    then err_ret fq else
    (t_close_quant vl' tl' f')
  in
  st_ret (vl, tl, f, close).

(* retrieve bound identifiers (useful to detect sharing) *)
Definition t_peek_bound (x: term_bound) : ident :=
  match x with
  | (v, _, _) => v.(vs_name)
  end.

Definition t_peek_branch (x: term_branch) : Sid.t :=
  match x with
  | (p, _, _) => Svs.fold (fun v a => Sid.add v.(vs_name) a) (pat_vars_of p) Sid.empty
  end.

Definition t_peek_quant (x: term_quant) : list ident :=
  match x with
  | (vl, _, _, _) => map (fun v => v.(vs_name)) vl
  end.

(* constructors with type checking *)

Local Open Scope errst_scope.

(*Basically, build up type susbstitution and ensure it matches*)
Definition ls_arg_inst (ls: lsymbol) (tl: list term_c) : 
  errorHashconsT ty_c (Mtv.t ty_c) :=
  let mtch s typ t :=
    t1 <- errst_lift2 (t_type t) ;;
    ty_match s typ t1 in
  o <- (fold_left2_errst mtch Mtv.empty ls.(ls_args) tl) ;;
  match o with
  | Some l => errst_ret l
  | None => errst_lift2 (throw (BadArity (ls, int_length tl)))
  end.

(*I think that we are claiming that it should have type typ, and
  getting the correct substitution (above does arguments, this does
  return type)*)
Definition ls_app_inst (ls: lsymbol) (tl: list term_c) (typ: option ty_c) :
   errorHashconsT ty_c (Mtv.t ty_c) :=
  s <- ls_arg_inst ls tl ;;
  match ls.(ls_value), typ with
  | Some _, None => errst_lift2 (throw (PredicateSymbolExpected ls))
  | None, Some _ => errst_lift2 (throw (FunctionSymbolExpected ls))
  | Some vty, Some typ => ty_match s vty typ
  | None, None => errst_ret s
  end.

Definition t_app_infer (ls: lsymbol) (tl: list term_c) : 
  errorHashconsT ty_c term_c :=
  s <- ls_arg_inst ls tl ;;
  let o := oty_inst s ls.(ls_value) in
  match o with
  | None => errst_ret (t_app1 ls tl None)
  | Some h =>
    h1 <- errst_lift1 h ;;
    errst_ret (t_app1 ls tl (Some h1))
  end.

Definition t_app ls tl typ :=
  _ <- ls_app_inst ls tl typ ;;
  errst_ret (t_app1 ls tl typ).

Definition fs_app fs tl ty := t_app fs tl (Some ty).
Definition ps_app ps tl := t_app ps tl None.

(*A bit of a hack*)
Definition AssertFail (s: string) : errtype :=
  mk_errtype "AssertFail" s.

Definition assert (b: bool) (msg : string) : errorM unit :=
  if b then err_ret tt else throw (AssertFail msg).

Definition assert_false {A: Type} (msg: string) : errorM A :=
  throw (AssertFail msg).

Local Open Scope err_scope.

Definition t_nat_const (n: CoqInt.int) : errorM term_c :=
  _ <-  (assert (CoqInt.ge n CoqInt.zero) "t_nat_const negative") ;;
  err_ret (t_const1 (ConstantDefs.int_const_of_int n) ty_int).

Definition t_int_const (n: CoqBigInt.t) : term_c :=
  t_const1 (ConstantDefs.int_const1 NumberDefs.ILitUnk n) ty_int.

(*TODO: for now, skip t_real_const - involves normalizing,
  Euclidean algo, see if we need*)

Definition t_string_const (s: string) : term_c :=
  t_const1 (ConstantDefs.string_const s) ty_str.

Definition InvalidIntegerLiteralType (t: ty_c) : errtype :=
  mk_errtype "InvalidIntegerLiteralType" t.
Definition InvalidRealLiteralType (t: ty_c) : errtype :=
  mk_errtype "InvalidRealLiteralType" t.
Definition InvalidStringLiteralType (t: ty_c) : errtype :=
  mk_errtype "InvalidStringLiteralType" t.

Import ConstantDefs.
Axiom check_float : NumberDefs.real_constant -> NumberDefs.float_format -> errorM unit.
(*NOTE: for now, we are not going to support floating points*)
Definition check_literal (c: constant) (t: ty_c) : errorM unit :=
  ts <- match (ty_node_of t), c with
    | Tyapp ts [], _ => err_ret ts
    | _, ConstInt _ => throw (InvalidIntegerLiteralType t)
    | _, ConstReal _ => throw (InvalidRealLiteralType t)
    |_ , ConstStr _ => throw (InvalidStringLiteralType t)
  end ;;
  match c, (ts_def_of ts) with
  (*Int*)
  | ConstInt n, NoDef => (*ts_int has type NoDef so this is safe*)
    if ts_equal ts ts_int then err_ret tt
    else throw (InvalidIntegerLiteralType t) 
  | ConstInt n, Range ir => NumberFuncs.check_range n ir
  | ConstInt n, _ => throw (InvalidIntegerLiteralType t) 
  (*Real*)
  | ConstReal _, NoDef => if ts_equal ts ts_real then err_ret tt
    else throw (InvalidRealLiteralType t)
  | ConstReal x, Float fp =>
    (*JOSH: TODO (or not) see*)
    check_float x fp
  | ConstReal _, _ => throw (InvalidRealLiteralType t)
  (*String*)
  | ConstStr _, _ => if ts_equal ts ts_str then err_ret tt
    else throw (InvalidStringLiteralType t)
  end.

Definition t_const c t : errorM term_c :=
  _ <- check_literal c t ;;
  err_ret (t_const1 c t).

Definition t_if (f t1 t2: term_c) : errorM term_c :=
  _ <- t_ty_check t1 (t_ty_of t1) ;;
  p <- t_prop f ;;
  err_ret (t_if1 p t1 t2).

Definition t_let (t1: term_c) (bt: term_bound) : errorM term_c :=
let '(v, _, t2) := bt in
  _ <- vs_check v t1 ;;
  err_ret (t_let1 t1 bt (t_ty_of t2)).

(*TODO: is err_listM equivalent to List.iter?*)

Definition EmptyCase : errtype :=
  mk_errtype "EmptyCase" tt.

Definition t_case (t: term_c) (bl: list term_branch) : errorM term_c :=
  tty <- t_type t ;;
  bty <- match bl with
          | (_, _, tbr) :: _ => err_ret (t_ty_of tbr)
          | _ => throw EmptyCase
          end ;;
  let t_check_branch (tb: term_branch) : errorM unit :=
    let '(p, _, tbr) := tb in
    _ <- ty_equal_check tty (pat_ty_of p) ;;
    t_ty_check tbr bty
  in
  _ <- errorM_list (map t_check_branch bl);;
  err_ret (t_case1 t bl bty).

Definition t_eps (bf: term_bound) : errorM term_c :=
  let '(v, _, f) := bf in
  _ <- t_prop f ;;
  err_ret (t_eps1 bf (Some v.(vs_ty))).

(*Note: term_quant only constructible via API so don't
  need to check type TODO ensure*)
Definition t_quant (q: quant) (qf: term_quant) : term_c :=
  let '(vl, _, _, f) := qf in
  if null vl then f else t_quant1 q qf.

Definition t_binary (op: binop) (f1 f2: term_c) : errorM term_c :=
  p1 <- t_prop f1 ;;
  p2 <- t_prop f2 ;;
  err_ret (t_binary1 op p1 p2).
  
Definition t_not (f: term_c) : errorM term_c :=
  p <- t_prop f ;;
  err_ret (t_not1 p).

Definition t_forall := t_quant Tforall.
Definition t_exists := t_quant Texists.
Definition t_and := t_binary Tand.
Definition t_or := t_binary Tor.
Definition t_implies := t_binary Timplies.
Definition t_iff := t_binary Tiff.

(*TODO: no check for single list error - is this a bug?
  I guess not as long as term is well-typed, but kind of
  weird to say singleton "and" can be a value-typed term*)
Fixpoint t_and_l (l: list term_c) : errorM term_c :=
  match l with
  | nil => err_ret t_true
  | [f] => err_ret f
  | f :: fl => 
    f1 <- (t_and_l fl) ;;
    t_and f f1
  end.

Fixpoint t_or_l (l: list term_c) : errorM term_c :=
  match l with
  | nil => err_ret t_false
  | [f] => err_ret f
  | f :: fl => 
    f1 <- (t_or_l fl) ;;
    t_or f f1
  end.
  
(*Skip async for now*)

(*Closing constructors*)

Definition t_quant_close (q: quant) (vl: list vsymbol) (tl: list (list term_c)) (f: term_c) :=
  if null vl then t_prop f else
  tq <- (t_close_quant vl tl f) ;;
  err_ret (t_quant q tq).

Definition t_forall_close := t_quant_close Tforall.
Definition t_exists_close := t_quant_close Texists.

Definition t_let_close (v: vsymbol) (t1 t2: term_c) : errorM term_c :=
  t_let t1 (t_close_bound v t2).
Definition t_case_close (t: term_c) (l: list (pattern_c * term_c)) :=
  t_case t (map (fun x => t_close_branch (fst x) (snd x)) l).
Definition t_eps_close (v: vsymbol) (f: term_c) :=
  t_eps (t_close_bound v f).

(*Built-in Symbols*)

Local Open Scope errst_scope.

(*These are pure functions because of our builtin types*)
Definition ps_equ : lsymbol :=
  create_psymbol_builtin (id_eq) [ty_a;ty_a].

(*Ignore ignore for now*)

Definition t_equ (t1 t2: term_c) : errorHashconsT ty_c term_c :=
  ps_app ps_equ [t1; t2].

Definition t_neq (t1 t2: term_c) : errorHashconsT ty_c term_c :=
  a <- (ps_app ps_equ [t1; t2]) ;;
  errst_lift2 (t_not a).

(*With builtin types, this is pure, not errorHashconsT*)
Definition fs_bool_true : lsymbol := 
  create_fsymbol_builtin (CoqBigInt.two) false
  id_true nil ty_bool.

Definition fs_bool_false : lsymbol :=
  create_fsymbol_builtin (CoqBigInt.two) false
  id_false nil ty_bool.
(*Don't use [fs_app] because this is a builtin*)
Definition t_bool_true : term_c := t_app1 fs_bool_true nil (Some ty_bool).
Definition t_bool_false : term_c := t_app1 fs_bool_false nil (Some ty_bool).

(*Convert boolean-valued term to prop (I believe)
  TODO: this seems a bit unsafe, make sure
  Ah, they just convert to (b = true) and type checking
  takes care of rest*)
Definition to_prop (t: term_c) : errorHashconsT ty_c term_c :=
  match (t_ty_of t) with
  | Some _ =>
    if t_equal t t_bool_true then errst_ret t_true
    else if t_equal t t_bool_false then errst_ret t_false
    else 
      t1 <- (t_equ t t_bool_true) ;;
      errst_ret (t_attr_copy t t1)
  | None => errst_ret t
  end.

(*TODO: skip tuples for now, can implement like type*)

Definition fs_func_app : lsymbol :=
  create_fsymbol_builtin CoqBigInt.zero false 
    id_app [ty_func_ab ; ty_a] ty_b.


Definition t_func_app (fn t: term_c) : errorHashconsT ty_c term_c :=
  t_app_infer fs_func_app [fn; t].
Definition t_pred_app pr t : errorHashconsT ty_c term_c :=
  t1 <- (t_func_app pr t) ;;
  t_equ t1 t_bool_true.

Definition t_func_app_l fn tl : errorHashconsT ty_c term_c :=
  foldl_errst t_func_app tl fn.

Definition t_pred_app_l pr tl : errorHashconsT ty_c term_c :=
  ta <- (t_func_app_l pr tl) ;;
  t_equ ta t_bool_true.

(*Skip acc and wf for now (can add later)*)

(*Subset of term library*)

(* fold over symbols *)

Fixpoint pat_gen_fold {A: Type} (fnT: A -> ty_c -> A) 
  (fnL: A -> lsymbol -> A) (acc : A) (pat : pattern_c) {struct pat} : A :=
  let fn acc p := pat_gen_fold fnT fnL acc p in
  let acc := fnT acc (pat_ty_of pat) in
  match pat_node_of pat with
    | Pwild => acc
    | Pvar _ => acc
    | Papp s pl => fold_left fn pl (fnL acc s)
    | Por p q => fn (fn acc p) q
    | Pas p _ => fn acc p
  end.

Fixpoint t_gen_fold {A: Type} (fnT : A -> ty_c -> A) (fnL: A -> lsymbol -> A) 
  (acc : A) (t : term_c) : A :=
  let fn := t_gen_fold fnT fnL in
  let acc := opt_fold fnT acc (t_ty_of t) in
  match t_node_of t with
  | Tconst _ => acc
  | Tvar _ => acc
  | Tapp f tl => fold_left fn tl (fnL acc f)
  | Tif f t1 t2 => fn (fn (fn acc f) t1) t2
  | Tlet t1 (_,_,t2) => fn (fn acc t1) t2
  | Tcase t1 bl =>
      let branch acc x :=
        fn (pat_gen_fold fnT fnL acc (fst (fst x))) (snd x) in
      fold_left branch bl (fn acc t1)
  | Teps (_, _, f) => fn acc f
  | Tquant _ (vl, _, tl, f1) =>
      (* these variables (and their types) may never appear below *)
      let acc := fold_left (fun a v => fnT a v.(vs_ty)) vl acc in
      fn (tr_fold fn acc tl) f1
  | Tbinop _ f1 f2 => fn (fn acc f1) f2
  | Tnot f1 => fn acc f1
  | Ttrue | Tfalse => acc
  end.

Definition t_s_fold {A: Type} := @t_gen_fold A.

Definition t_ty_fold {A: Type} (fn: A -> ty_c -> A) (acc: A) (t: term_c) : A :=
  t_s_fold fn (fun x _ => x) acc t.

Definition t_ty_freevars := t_ty_fold ty_freevars.

(*Polarity map*)


Definition t_map_sign_errst_unsafe {St: Type}
  (fn: bool -> term_c -> errState St term_c)  (sign: bool) (f: term_c) :
  errState St term_c :=  
  (match t_node_of f with
| Tbinop Timplies f1 f2 =>
    f1' <- fn (negb sign) f1 ;;
    f2' <- fn sign f2 ;;
    t1 <- errst_lift2 (t_implies f1' f2') ;;
    errst_ret (t_attr_copy f t1)
| Tbinop Tiff f1 f2 =>
    f1p <- fn sign f1 ;;
    f1n <- fn (negb sign) f1 ;;
    f2p <- fn sign f2 ;; 
    f2n <- fn (negb sign) f2 ;;
    if t_equal f1p f1n && t_equal f2p f2n then 
      t1 <- errst_lift2 (t_iff f1p f2p) ;;
      errst_ret (t_attr_copy f t1)
    else if sign
      then 
        t1 <- errst_lift2 (t_implies f1n f2p) ;;
        t2 <- errst_lift2 (t_implies f2n f1p) ;;
        t3 <- errst_lift2 (t_and t1 t2) ;;
        errst_ret (t_attr_copy f t3)
      else 
        t1 <- errst_lift2 (t_or f1n f2n) ;;
        t2 <- errst_lift2 (t_and f1p f2p) ;;
        t3 <- errst_lift2 (t_implies t1 t2) ;;
        errst_ret (t_attr_copy f t3)
    (*t_attr_copy f*)
| Tnot f1 =>
    f1' <- (fn (negb sign) f1) ;;
    t1 <- errst_lift2 (t_not f1') ;;
    errst_ret (t_attr_copy f t1)
| Tif f1 f2 f3 =>  if negb (isSome (t_ty_of f)) then
    f1p <- fn sign f1 ;; 
    f1n <- fn (negb sign) f1 ;;
    f2 <- fn sign f2 ;; 
    f3 <- fn sign f3 ;;
    if t_equal f1p f1n then 
      t1 <- errst_lift2 (t_if f1p f2 f3) ;;
      errst_ret (t_attr_copy f t1)
    else if sign then 
      t1 <- errst_lift2 (t_implies f1n f2) ;;
      t2 <- errst_lift2 (t_not f1p) ;;
      t3 <- errst_lift2 (t_implies t2 f3) ;;
      t4 <- errst_lift2 (t_and t1 t3) ;;
      errst_ret (t_attr_copy f t4)
    else 
      t1 <- errst_lift2 (t_and f1p f2) ;;
      t2 <- errst_lift2 (t_not f1n) ;;
      t3 <- errst_lift2 (t_and t2 f3) ;;
      t4 <- errst_lift2 (t_or t1 t3) ;;
      errst_ret (t_attr_copy f t4)
  else errst_throw (Failure "t_map_sign: cannot determine polarity")
| Teps _ => errst_throw (Failure "t_map_sign: cannot determine polarity")
| _ => 
  t1 <- (t_map_errst_unsafe (fn sign) f) ;;
  errst_ret (t_attr_copy f t1)
end).

(* map/fold over free variables *)
(*Only fold for now*)

Definition bnd_v_fold {A: Type} (fn: A -> vsymbol -> A) (acc: A) 
  (b: bind_info) : A :=
    Mvs.fold (fun v _ acc => fn acc v) b.(bv_vars) acc.

Definition bound_v_fold {A B C: Type} (fn: A -> vsymbol -> A) (acc: A)
  (x : B * bind_info * C) : A :=
  let '(_, b, _) := x in
  bnd_v_fold fn acc b.

Fixpoint t_v_fold {A: Type} (fn : A -> vsymbol -> A) (acc: A)
  (t: term_c) : A :=
  match (t_node_of t) with
  | Tvar v => fn acc v
  | Tlet e b => bound_v_fold fn (t_v_fold fn acc e) b
  | Tcase e bl => fold_left (bound_v_fold fn) bl (t_v_fold fn acc e)
  | Teps b => bound_v_fold fn acc b
  | Tquant _ (_, b, _, _) => bnd_v_fold fn acc b (*No recursion bc we know free vars*)
  | _ => t_fold_unsafe (t_v_fold fn) acc t
  end.

Definition t_v_all (pr: vsymbol -> bool) (t: term_c) : bool :=
  t_v_fold (fun x v => x && pr v) true t.

Definition bnd_v_count {A: Type} (fn: A -> vsymbol -> CoqBigInt.t -> A) acc b := 
  Mvs.fold (fun v n acc => fn acc v n) b.(bv_vars) acc.

(* let bound_v_count fn acc x :=
  t_view_bound 

 ((_,b),_) = bnd_v_count fn acc b *)

Fixpoint t_v_count {A: Type} (fn: A -> vsymbol -> CoqBigInt.t -> A) (acc: A) (t: term_c) : A :=
  match t_node_of t with
  | Tvar v => fn acc v CoqBigInt.one
  | Tlet e (_, b, _) => bnd_v_count fn (t_v_count fn acc e) b
  | Tcase e bl => fold_left (bnd_v_count fn) (map (fun x => snd (fst x)) bl) (t_v_count fn acc e)
  | Teps (_, b, _) => bnd_v_count fn acc b
  | Tquant _ (((_,b),_),_) => bnd_v_count fn acc b
  | _ => t_fold_unsafe (t_v_count fn) acc t
  end.

Definition t_v_occurs v t :=
  t_v_count (fun c u n => if vs_equal u v then CoqBigInt.add c n else c) CoqBigInt.zero t.

(* replaces variables with terms in term [t] using map [m] *)

(*NOTE: we need to iterate over bindings, not map directly*)
(*NOTE: these are still somewhat unsafe (but OK for our purposes here), versions 
  in TermTraverse.v are safe*)
Definition t_subst m t : errorM term_c := 
  (_ <- (iter_err (fun x => vs_check (fst x) (snd x)) (Mvs.bindings m)) ;;
  err_ret (t_subst_unsafe m t))%err.

Definition t_subst_single v t1 t := t_subst (Mvs.singleton _ v t1) t.

(** Traversal with separate functions for value-typed and prop-typed terms *)
(*TODO: temp: Alt module until we replace the rest*)
Module TermTFAlt.

Definition t_select {A: Type} (fnT: term_c -> A) (fnF: term_c -> A) 
  (e: term_c) : A :=
  if isNone (t_ty_of e) then fnF e else fnT e.

Definition t_selecti {A B: Type} (fnT: A -> term_c -> B) 
  (fnF: A -> term_c -> B) (acc: A) (e: term_c) : B :=
  if isNone (t_ty_of e) then fnF acc e else fnT acc e.

Definition t_map_errst_unsafe {St: Type} (fnT: term_c -> errState St term_c) (fnF: term_c -> errState St term_c) := 
  t_map_errst_unsafe (t_select fnT fnF).

Definition t_map_sign_errst_unsafe {St: Type} (fnT: bool -> term_c -> errState St term_c)
  (fnF: bool -> term_c -> errState St term_c) : bool -> term_c -> errState St term_c :=
  t_map_sign_errst_unsafe (t_selecti fnT fnF).

Definition tr_map_errst {St: Type} (fnT: term_c -> errState St term_c) (fnF: term_c -> errState St term_c) :=
  tr_map_errst (t_select fnT fnF).

End TermTFAlt.

(*NOTE: this is a unsafe traversal function, only for use in Coq where we can prove
  that it is used safely. The general version is in TermTraverse.v. It is much more
  complicated because it uses state and is not structurally recursive*)
Section TermRecUnsafe.
Context {A: Type}
  (var_case: vsymbol -> A)
  (const_case: constant -> A)
  (app_case: lsymbol -> list term_c -> list A -> A)
  (if_case: term_c -> A -> term_c -> A -> term_c -> A -> A)
  (let_case: term_c -> A -> vsymbol -> term_c -> A -> A)
  (match_case : term_c -> A -> (list (pattern_c * term_c * A)) -> A)
  (eps_case: vsymbol -> term_c -> A -> A)
  (quant_case: quant -> list vsymbol -> term_c -> A -> A)
  (binop_case: binop -> term_c -> A -> term_c -> A -> A)
  (not_case: term_c -> A -> A)
  (true_case: A)
  (false_case : A).
Fixpoint term_rec (t: term_c) : A :=
  match t_node_of t with
  | Tvar v => var_case v
  | Tconst c => const_case c
  | Tapp l ts => app_case l ts (map term_rec ts)
  | Tif t1 t2 t3 => if_case t1 (term_rec t1) t2 (term_rec t2) t3 (term_rec t3)
  | Tlet t1 (v, _, t2) => let_case t1 (term_rec t1) v t2 (term_rec t2)
  | Tcase t1 ps => match_case t1 (term_rec t1) (map (fun x => (fst (fst x), (snd x), term_rec (snd x))) ps)
  | Teps (v, _, f) => eps_case v f (term_rec f)
  | Tquant q (vs, _, _, f) => quant_case q vs f (term_rec f)
  | Tbinop b t1 t2 => binop_case b t1 (term_rec t1) t2 (term_rec t2)
  | Tnot f => not_case f (term_rec f)
  | Ttrue => true_case
  | Tfalse => false_case
  end.
End TermRecUnsafe.

(* constructors with propositional simplification *)

(*TODO for this (and below) should we be in error monad?
  This is not type safe if we give (e.g) t_and Ttrue (foo a), where foo is not Prop
  So spec is: if both are typed Prop, then this is semantically equal to And (and similar)
  have:
  1. produces well-typed term if no error reached
  2. if inputs were well typed prop, produces semantically equal to and
  3. no spec if not - need to prove precondition*)
Definition t_not_simp (f: term_c) : errorM term_c := 
  match t_node_of f with
  | Ttrue  => err_ret (t_attr_copy f t_false)
  | Tfalse => err_ret (t_attr_copy f t_true)
  | Tnot g => err_ret (t_attr_copy f g)
  | _      => t_not f
  end.

Definition t_and_simp (f1 f2 : term_c) : errorM term_c := 
  match t_node_of f1, t_node_of f2 with
  | Ttrue, _  => err_ret f2
  | _, Ttrue  => err_ret (t_attr_remove_name "asym_split" f1)
  | Tfalse, _ => err_ret (t_attr_remove_name "asym_split" f1)
  | _, Tfalse => err_ret f2
  | _, _ => if t_equal f1 f2 then err_ret f1 else t_and f1 f2
  end.

Definition t_or_simp (f1 f2 : term_c) : errorM term_c := 
  match t_node_of f1, t_node_of f2 with
  | Ttrue, _  => err_ret (t_attr_remove_name "asym_split" f1)
  | _, Ttrue  => err_ret f2
  | Tfalse, _ => err_ret f2
  | _, Tfalse => err_ret (t_attr_remove_name "asym_split" f1)
  | _, _ => if t_equal f1 f2 then err_ret f1 else t_or f1 f2
  end.

Definition t_implies_simp (f1 f2 : term_c) : errorM term_c :=
 match t_node_of f1, t_node_of f2 with
  | Ttrue, _  => err_ret f2
  | _, Ttrue  => err_ret f2
  | Tfalse, _ => err_ret (t_attr_copy f1 t_true)
  | _, Tfalse => t_not_simp f1
  | _, _ => if t_equal f1 f2 then err_ret (t_attr_copy f1 t_true) else t_implies f1 f2
 end.

Definition t_iff_simp (f1 f2 : term_c) : errorM term_c := 
  match t_node_of f1, t_node_of f2 with
  | Ttrue, _  => err_ret f2
  | _, Ttrue  => err_ret f1
  | Tfalse, _ => t_not_simp f2
  | _, Tfalse => t_not_simp f1
  | _, _ => if t_equal f1 f2 then err_ret (t_attr_copy f1 t_true) else t_iff f1 f2
  end.

(*Removes unused vars*)
Definition t_quant_close_simp (q: quant) (vl : list vsymbol) (tl : list (list term_c)) (f: term_c) :
  errorM term_c :=
  if null vl then err_ret f else
  let fvs := t_vars f in
  let check v := Mvs.mem v fvs in
  if forallb check vl then
    t_quant_close q vl tl f
  else
    let vl := filter check vl in
    if null vl  then err_ret f
    else t_quant_close q vl (filter (forallb (t_v_all check)) tl) f.

Definition t_forall_close_simp := t_quant_close_simp Tforall.
Definition t_exists_close_simp := t_quant_close_simp Texists.

Definition t_equ_simp (t1 t2 : term_c) : errorHashconsT ty_c term_c :=
  if t_equal t1 t2 then errst_ret t_true  else t_equ t1 t2.

Definition small t := 
  match t_node_of t with
  | Tvar _ | Tconst _ => true
(* NOTE: shouldn't we allow this?
  | Tapp (_,[]) -> true
*)
  | _ => false
end.

(*Just do false version for now*)

Definition t_let_close_simp (v: vsymbol) (e t: term_c) : errorM term_c :=
  let n := t_v_occurs v t in
  if CoqBigInt.is_zero n then err_ret t
  else
  if CoqBigInt.eqb n CoqBigInt.one || small e then
    t_subst_single v e t
  else
    t_let_close v e t.

Definition t_quant_simp1 (q: quant) (qf: term_quant) : errorM term_c :=
  let '(vl, _, _, f) := qf in
  let fvs := t_vars f in
  let check v := Mvs.mem v fvs in
  if forallb check vl then
    err_ret (t_quant q qf)
  else
    let '(vl,tl,f) := t_view_quant qf in
    let fvs := t_vars f in
    let check v := Mvs.mem v fvs in
    let vl := filter check vl in
    if null vl then err_ret f
    else t_quant_close q vl (filter (forallb (t_v_all check)) tl) f.