Require Import Monads IntFuncs. 
Require Export IdentDefs TyDefs.
From ExtLib Require Import Monads.
Import MonadNotations.
Local Open Scope state_scope.

(*First, deal with builtins, because we want to add them directly
  for hashconsing. This ensures that e.g. ty_bool is a pure
  value, not wrapped in a monad*)

Definition ty_var_builtin (n: tvsymbol) (tag: CoqWeakhtbl.tag) :
  ty_c := mk_ty_c (Tyvar n) tag.
Definition ty_app_builtin (s: tysymbol_c) (tl: list ty_c)
  (tag: CoqWeakhtbl.tag) : ty_c :=
  mk_ty_c (Tyapp s tl) tag.


(* built-in symbols *)

Definition mk_ts_builtin (name: ident) (args: list tvsymbol) (d: type_def ty_c) : 
  tysymbol_c := mk_ts_c name args d.


(*NOTE: for these, we actually know that they will not fail,
  so we define manually, not with [create_tysymbol].
  TODO (maybe): reserve counter values for builtins so that
  we don't need ctr state here either*)
Definition ts_int := mk_ts_builtin id_int nil NoDef.
Definition ts_real := mk_ts_builtin id_real nil NoDef.
Definition ts_bool := mk_ts_builtin id_bool nil NoDef.
Definition ts_str := mk_ts_builtin id_str nil NoDef.

(*Similarly, we know that ty_app will succeed,
  but we still need hashconsing*)
(*NOTE: if we want, we could add these values to the
  hashcons map at the beginning; then we would not need
  state here
  TODO see if this is needed/helpful*)
Definition ty_int := ty_app_builtin ts_int nil 
  (CoqWeakhtbl.create_tag (CoqBigInt.one)).
Definition ty_real := ty_app_builtin ts_real nil
  (CoqWeakhtbl.create_tag (CoqBigInt.two)).
Definition ty_bool := ty_app_builtin ts_bool nil
  (CoqWeakhtbl.create_tag (CoqBigInt.three)).
Definition ty_str := ty_app_builtin ts_str nil
  (CoqWeakhtbl.create_tag (CoqBigInt.four)).

Definition create_builtin_tvsymbol (i: ident) : tvsymbol :=
  {| tv_name := i|}.

Definition ts_func :=
  let tv_a := create_builtin_tvsymbol id_a in
  let tv_b := create_builtin_tvsymbol id_b in
  mk_ts_builtin id_fun [tv_a; tv_b] NoDef.

(*And type variables*)
Definition vs_a : tvsymbol :=
  (create_tvsymbol_builtin id_a).
Definition vs_b : tvsymbol :=
  (create_tvsymbol_builtin id_b).
Definition vs_c : tvsymbol :=
  (create_tvsymbol_builtin id_c).
Definition vs_d : tvsymbol :=
  (create_tvsymbol_builtin id_d).
Definition vs_e : tvsymbol :=
  (create_tvsymbol_builtin id_e).
Definition vs_f : tvsymbol :=
  (create_tvsymbol_builtin id_f).
Definition vs_g : tvsymbol :=
  (create_tvsymbol_builtin id_g).
Definition vs_h : tvsymbol :=
  (create_tvsymbol_builtin id_h).
Definition vs_i : tvsymbol :=
  (create_tvsymbol_builtin id_i).
Definition vs_j : tvsymbol :=
  (create_tvsymbol_builtin id_j).
Definition vs_k : tvsymbol :=
  (create_tvsymbol_builtin id_k).
Definition vs_l : tvsymbol :=
  (create_tvsymbol_builtin id_l).
Definition vs_m : tvsymbol :=
  (create_tvsymbol_builtin id_m).
Definition vs_n : tvsymbol :=
  (create_tvsymbol_builtin id_n).
Definition vs_o : tvsymbol :=
  (create_tvsymbol_builtin id_o).
Definition vs_p : tvsymbol :=
  (create_tvsymbol_builtin id_p).
Definition vs_q : tvsymbol :=
  (create_tvsymbol_builtin id_q).
Definition vs_r : tvsymbol :=
  (create_tvsymbol_builtin id_r).
Definition vs_s : tvsymbol :=
  (create_tvsymbol_builtin id_s).
Definition vs_t : tvsymbol :=
  (create_tvsymbol_builtin id_t).

Definition vs_a1 : tvsymbol :=
  (create_tvsymbol_builtin id_a1).
Definition vs_a2 : tvsymbol :=
  (create_tvsymbol_builtin id_a2).
Definition vs_a3 : tvsymbol :=
  (create_tvsymbol_builtin id_a3).
Definition vs_a4 : tvsymbol :=
  (create_tvsymbol_builtin id_a4).
Definition vs_a5 : tvsymbol :=
  (create_tvsymbol_builtin id_a5).
Definition vs_a6 : tvsymbol :=
  (create_tvsymbol_builtin id_a6).
Definition vs_a7 : tvsymbol :=
  (create_tvsymbol_builtin id_a7).
Definition vs_a8 : tvsymbol :=
  (create_tvsymbol_builtin id_a8).
Definition vs_a9 : tvsymbol :=
  (create_tvsymbol_builtin id_a9).
Definition vs_b0 : tvsymbol :=
  (create_tvsymbol_builtin id_b0).
Definition vs_b1 : tvsymbol :=
  (create_tvsymbol_builtin id_b1).
Definition vs_b2 : tvsymbol :=
  (create_tvsymbol_builtin id_b2).
Definition vs_b3 : tvsymbol :=
  (create_tvsymbol_builtin id_b3).
Definition vs_b4 : tvsymbol :=
  (create_tvsymbol_builtin id_b4).
Definition vs_b5 : tvsymbol :=
  (create_tvsymbol_builtin id_b5).
Definition vs_b6 : tvsymbol :=
  (create_tvsymbol_builtin id_b6).



Definition ty_a : ty_c :=
  ty_var_builtin vs_a
    (CoqWeakhtbl.create_tag (CoqBigInt.five)).
Definition ty_b : ty_c :=
  ty_var_builtin vs_b
    (CoqWeakhtbl.create_tag (CoqBigInt.six)).

(*One particular function type is builtin (the general case
  is below)*)
Definition ty_func_ab : ty_c :=
  ty_app_builtin ts_func [ty_a; ty_b]
    (CoqWeakhtbl.create_tag (CoqBigInt.seven)).

(*Now construct hashcons with these builtin values*)
(*TODO: see note in IdentDefs.ty, need to ensure this is
  called in Coq*)
Definition ty_hashcons_builtins : hashcons_st ty_c unit :=
  Hsty.add_builtins
  [ty_int; ty_real; ty_bool; ty_str; ty_a; ty_b; ty_func_ab] 
    (CoqBigInt.eight).

Definition mk_ty (n: ty_node_c) : ty_c :=
  mk_ty_c n CoqWeakhtbl.dummy_tag.

Definition ty_var (n: tvsymbol) : hashcons_st _ ty_c :=
  Hsty.hashcons (mk_ty (Tyvar n)).
Definition ty_app1 (s: tysymbol_c) (tl: list ty_c) : hashcons_st _ ty_c :=
  Hsty.hashcons (mk_ty (Tyapp s tl)).
Definition ty_app_unsafe (s: tysymbol_c) (tl: list ty_c) : ty_c :=
   (mk_ty (Tyapp s tl)).

(*Generic Traversal Functions*)
(*The reason we actually do want hash consing, or else
  the counter grows every time we call one of these functions*)
Definition ty_map (fn: ty_c -> ty_c) (t: ty_c) : hashcons_st _ ty_c :=
  match ty_node_of t with
  | Tyvar _ => st_ret t
  | Tyapp f tl => ty_app1 f (map fn tl)
  end.

Definition ty_map_unsafe (fn: ty_c -> ty_c) (t: ty_c) : ty_c :=
  match ty_node_of t with
  | Tyvar _ => t
  | Tyapp f tl => ty_app_unsafe f (map fn tl)
  end.

Definition ty_fold {A: Type} (fn: A -> ty_c -> A) (acc: A) (t: ty_c) : A :=
  match ty_node_of t with
  | Tyvar _ => acc
  | Tyapp _ tl => List.fold_left fn tl acc
  end.

Definition ty_all (pr: ty_c -> bool) (t: ty_c) : bool :=
  ty_fold (fun acc x => acc && (pr x)) true t.

Definition ty_any (pr: ty_c -> bool) (t: ty_c) : bool :=
  ty_fold (fun acc x => acc || (pr x)) false t.

Definition type_def_map {A: Type} (fn: A -> A) (x: type_def A) : type_def A :=
  match x with
  | Alias t => Alias (fn t)
  | _ => x
  end.

Definition type_def_fold {A B: Type} (fn: A -> B -> A) (acc: A) 
  (t: type_def B) : A :=
  match t with
  | Alias t => fn acc t
  | _ => acc
  end.

Definition is_alias_type_def {A: Type} (t: type_def A) : bool :=
  match t with
  | Alias _ => true
  | _ => false
  end.

Definition is_range_type_def {A: Type} (t: type_def A) : bool :=
  match t with
  | Range _ => true
  | _ => false
  end.

Definition is_float_type_def {A: Type} (t: type_def A) : bool :=
  match t with
  | Float _ => true
  | _ => false
  end.

(*Traversal Functions on Type Variables*)
Fixpoint ty_v_map (fn: tvsymbol -> ty_c) (t: ty_c) : hashcons_st _ ty_c :=
  match ty_node_of t with
  | Tyvar v => st_ret (fn v)
  | Tyapp f tl => 
    l <- st_list (map (ty_v_map fn) tl) ;;
    ty_app1 f l
  end.

Fixpoint ty_v_fold {A: Type} (fn: A -> tvsymbol -> A) (acc: A)
  (t: ty_c) : A :=
  match ty_node_of t with
  | Tyvar v => fn acc v
  | Tyapp _ tl => List.fold_left (ty_v_fold fn) tl acc
  end.

Definition ty_v_all (pr: tvsymbol -> bool) (t: ty_c) : bool :=
  ty_v_fold (fun acc v => acc && (pr v)) true t.

Definition ty_v_any (pr: tvsymbol -> bool) (t: ty_c) : bool :=
  ty_v_fold (fun acc v => acc || (pr v)) false t.
Fixpoint ty_v_map_err (fn: tvsymbol -> errorM ty_c) (t: ty_c) :
  errorHashconsT ty_c ty_c :=
  (match ty_node_of t with
  | Tyvar v => errst_lift2 (fn v)
  | Tyapp f tl =>
    l <- errst_list (map (ty_v_map_err fn) tl) ;;
    errst_lift1 (ty_app1 f l)
  end)%errst.

Definition ty_full_inst (m: Mtv.t ty_c) (t: ty_c) : errorHashconsT ty_c ty_c:=
  ty_v_map_err (fun v => Mtv.find _ v m) t.

Definition ty_freevars (s: Stv.t) (t: ty_c) : Stv.t :=
  ty_v_fold Stv.add_left s t.

Definition ty_closed (t: ty_c) : bool :=
  ty_v_all (fun _ => false) t.

(*Smart constructors*)

Definition BadTypeArity (t: tysymbol_c * CoqBigInt.t) : errtype := 
  mk_errtype "BadTypeArity" t.

Definition DuplicateTypeVar (t: tvsymbol) : errtype := 
  mk_errtype "DuplicateTypeVar" t.

Local Open Scope err_scope.

(*TODO: replace with this?*)
Fixpoint ty_v_fold_err {A: Type} (fn: A -> tvsymbol -> errorM A) (acc: A)
  (t: ty_c) {struct t} : errorM A :=
  match ty_node_of t with
  | Tyvar v => fn acc v
  | Tyapp _ tl => foldr_err (ty_v_fold_err fn) tl acc
  end.

Definition ty_v_all_err (pr: tvsymbol -> errorM bool) (t: ty_c) : 
  errorM bool :=
  ty_v_fold_err (fun acc v => 
    i <- pr v ;;
    err_ret (i && acc)) true t.

Definition UnboundTypeVar (t: tvsymbol) : errtype := 
  mk_errtype "UnboundTypeVar" t.

Definition IllegalTypeParameters : errtype := 
  mk_errtype "IllegalTypeParameters" tt.
Definition EmptyRange : errtype := mk_errtype "EmptyRange" tt.
Definition BadFloatSpec : errtype := mk_errtype "BadFloatSpec" tt.

Definition create_tysymbol (name: preid) (args: list tvsymbol) (d: type_def ty_c) (*: tysymbol_c*)
  : errorM (ctr tysymbol_c) :=
  let add (s: Stv.t) (v: tvsymbol) := Stv.add_new (DuplicateTypeVar v) v s in
  let s1 := foldr_err add args Stv.empty in
  let check (v: tvsymbol) : errorM bool := 
    m <- s1 ;;
    if Stv.mem v m then err_ret true else
    throw (UnboundTypeVar v)
  in
  let c: errorM unit :=
    match d with
    | NoDef => err_ret tt
    | Alias d' => 
      ignore (ty_v_all_err check d')
    | Range ir =>
      if negb (null args) then
        throw IllegalTypeParameters
      else if CoqBigInt.lt ir.(NumberDefs.ir_upper) ir.(NumberDefs.ir_lower)
        then throw EmptyRange
      else err_ret tt
    | Float fp => if negb (null args) then
        throw IllegalTypeParameters
      else if CoqBigInt.lt fp.(NumberDefs.fp_exponent_digits) CoqBigInt.one ||
        CoqBigInt.lt (fp.(NumberDefs.fp_significand_digits)) CoqBigInt.one then
        throw BadFloatSpec
      else err_ret tt
    end in
  _ <- c ;;
  err_ret (mk_ts name args d).

(*Returns map of type variables to elements in list tl*)
Definition ts_match_args {A: Type} (s: tysymbol_c) (tl: list A) : 
  errorM (Mtv.t A) :=
  match fold_right2 Mtv.add (ts_args_of s) tl Mtv.empty with
  | Some m => err_ret m
  | None => throw (BadTypeArity (s, int_length tl))
  end.

Definition ty_match_args (t: ty_c) : errorM (Mtv.t ty_c) :=
  match ty_node_of t with
  | Tyapp s tl => ts_match_args s tl
  | _ => throw (Invalid_argument "Ty.ty_match_args")
  end.

Definition ty_app (s: tysymbol_c) (tl: list ty_c) : errorHashconsT ty_c ty_c :=
  match ts_def_of s with
  | Alias t => 
    (m <- (errst_lift2 (ts_match_args s tl)) ;;
    ty_full_inst m t)%errst
  | _ =>
    if negb (CoqBigInt.eqb (int_length (ts_args_of s)) (int_length tl)) then
      (errst_lift2 (throw (BadTypeArity (s, int_length tl))))
    else errst_lift1 (ty_app1 s tl)
  end.


(* symbol-wise map/fold *)
Fixpoint ty_s_map (fn: tysymbol_c -> tysymbol_c) (t: ty_c) : errorHashconsT ty_c ty_c :=
  match ty_node_of t with
  | Tyvar _ => errst_ret t
  | Tyapp f tl => 
    (l <- (errst_list (map (ty_s_map fn) tl)) ;;
    ty_app (fn f) l)%errst
  end.

Fixpoint ty_s_fold {A: Type} (fn: A -> tysymbol_c -> A) (acc: A) (t: ty_c) : A :=
  match ty_node_of t with
  | Tyvar _ => acc
  | Tyapp f tl => List.fold_left (ty_s_fold fn) tl (fn acc f)
  end.

Definition ty_s_all (pr: tysymbol_c -> bool) (t: ty_c) : bool :=
  ty_s_fold (fun x y => x && (pr y)) true t.
Definition ty_s_any (pr: tysymbol_c -> bool) (t: ty_c) : bool :=
  ty_s_fold (fun x y => x || (pr y)) false t.

(* type matching *)
(* Local Open Scope state_scope (*TODO: fix scopes*). *)
(*TODO: very bad*)
Definition ty_mapM (fn: ty_c -> hashcons_st _ ty_c) (t: ty_c) : hashcons_st _ ty_c :=
  match ty_node_of t with
  | Tyvar _ => st_ret t
  | Tyapp f tl => 
    (l <- st_list (map fn tl) ;;
    ty_app1 f l)%state
end.

(*TODO: why does this pass Coq's termination checker?*)
(*Idea: instantiate type variables from the map*)
Fixpoint ty_inst (s: Mtv.t ty_c) (t: ty_c) : hashcons_st _ ty_c :=
  match ty_node_of t with
  | Tyvar n => st_ret (Mtv.find_def _ t n s)
  | _ => ty_mapM (ty_inst s) t
  end.

Fixpoint ty_inst_unsafe (s: Mtv.t ty_c) (t: ty_c) : ty_c :=
  match ty_node_of t with
  | Tyvar n => Mtv.find_def _ t n s
  | _ => ty_map_unsafe (ty_inst_unsafe s) t
  end.

Definition Exit : errtype := mk_errtype "Exit" tt.

(*Version with exceptions*)
(*Write in strange way so Coq can use in nested recursion*)
Definition fold_right2_error := fun {A B C: Type} (f: C -> A -> B -> errorM C) =>
  fix fold_right2_error (l1: list A) (l2: list B) (accu: C) {struct l1} : errorM C :=
  match l1, l2 with
  | nil, nil => err_ret accu
  | a1 :: l1, a2 :: l2 => 
    x <- fold_right2_error l1 l2 accu ;;
    f x a1 a2
  | _, _ => throw (Invalid_argument "fold_right2")
  end.

Definition TypeMismatch (t: ty_c * ty_c) : errtype := 
  mk_errtype "TypeMismatch" t.

(*Idea: when we have variable: check to see if it is in map
  If so, must be mapped to ty2 or else throw exception*)
(*We add an extra parameter in a bit of a hack so that 
  we throw the exception that the higher-level interface
  expects (since we don't have try/catch)*)
Fixpoint ty_match_aux (*(err1 err2: ty_c) *)
  (s: Mtv.t ty_c) (ty1 ty2: ty_c) 
   : errorM (Mtv.t ty_c) :=

  match ty_node_of ty1, ty_node_of ty2 with
  | Tyapp f1 l1, Tyapp f2 l2 =>
    if ts_equal f1 f2 then
    fold_right2_error (ty_match_aux (*err1 err2*)) l1 l2 s
    else throw Exit (*(TypeMismatch (err1, err2))*)
  | Tyvar n1, _ => 
    (*We are not using Mtv.change because there is an
      exception in the function (so the types do not match)
      Instead, we will search manually and throw an exception if needed*)
    match Mtv.find_opt n1 s with
    | Some ty3 => if ty_equal ty3 ty2 then err_ret s else
      throw Exit (*
      throw (TypeMismatch (err1, err2))*)
    | None => err_ret (Mtv.add n1 ty2 s)
    end
  | _, _ => throw Exit (*throw (TypeMismatch (err1, err2))*)
  end.

Definition ty_match  (s: Mtv.t ty_c) (ty1 ty2: ty_c) : errorHashconsT _ (Mtv.t ty_c) :=
  (t1 <- (errst_lift1 (ty_inst s ty1)) ;;
  errst_lift2
  (trywith (fun (_ : unit) => (ty_match_aux s ty1 ty2)) Exit 
    (fun (_: unit) => throw (TypeMismatch (t1, ty2)))))%errst.

(*These must be hashconsed because they are not constant*)
(*We know that [ty_app] always succeeds here*)
Definition ty_func (ty_a ty_b: ty_c) : hashcons_st _ ty_c :=
  ty_app1 ts_func [ty_a; ty_b].

Definition ty_pred (ty_a : ty_c) : hashcons_st _ ty_c := 
  ty_app1 ts_func [ty_a; ty_bool].

(*Tuples*)

(*TODO: just hard code in the tuples*)

(*Tuple typesyms*)
Definition ts_tuple0: tysymbol_c := mk_ts_builtin id_tup0 [] NoDef.
Definition ts_tuple1 : tysymbol_c := mk_ts_builtin id_tup1 [vs_a] NoDef.
Definition ts_tuple2 : tysymbol_c := mk_ts_builtin id_tup2 [vs_a; vs_b] NoDef.
Definition ts_tuple3 : tysymbol_c := mk_ts_builtin id_tup3 [vs_a; vs_b; vs_c] NoDef.
Definition ts_tuple4 : tysymbol_c := mk_ts_builtin id_tup4 [vs_a; vs_b; vs_c; vs_d] NoDef.
Definition ts_tuple5 : tysymbol_c := mk_ts_builtin id_tup5 [vs_a; vs_b; vs_c; vs_d; vs_e] NoDef.
Definition ts_tuple6 : tysymbol_c := mk_ts_builtin id_tup6 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f] NoDef.
Definition ts_tuple7 : tysymbol_c := mk_ts_builtin id_tup7 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g] NoDef.
Definition ts_tuple8 : tysymbol_c := mk_ts_builtin id_tup8 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h] NoDef.
Definition ts_tuple9 : tysymbol_c := mk_ts_builtin id_tup9 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i] NoDef.
Definition ts_tuple10 : tysymbol_c := mk_ts_builtin id_tup10 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j] NoDef.
Definition ts_tuple11 : tysymbol_c := mk_ts_builtin id_tup11 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k] NoDef.
Definition ts_tuple12 : tysymbol_c := mk_ts_builtin id_tup12 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l] NoDef.
Definition ts_tuple13 : tysymbol_c := mk_ts_builtin id_tup13 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m] NoDef.
Definition ts_tuple14 : tysymbol_c := mk_ts_builtin id_tup14 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n] NoDef.
Definition ts_tuple15 : tysymbol_c := mk_ts_builtin id_tup15 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o] NoDef.
Definition ts_tuple16 : tysymbol_c := mk_ts_builtin id_tup16 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p] NoDef.
Definition ts_tuple17 : tysymbol_c := mk_ts_builtin id_tup17 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q] NoDef.
Definition ts_tuple18 : tysymbol_c := mk_ts_builtin id_tup18 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r] NoDef.
Definition ts_tuple19 : tysymbol_c := mk_ts_builtin id_tup19 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s] NoDef.
Definition ts_tuple20 : tysymbol_c := mk_ts_builtin id_tup20 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s; vs_t] NoDef.

Definition ts_tuple21 : tysymbol_c := mk_ts_builtin id_tup21 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s; vs_t;
  vs_a1] NoDef.
Definition ts_tuple22 : tysymbol_c := mk_ts_builtin id_tup22 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s; vs_t;
  vs_a1; vs_a2] NoDef.
Definition ts_tuple23 : tysymbol_c := mk_ts_builtin id_tup23 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s; vs_t;
  vs_a1; vs_a2; vs_a3] NoDef.
Definition ts_tuple24 : tysymbol_c := mk_ts_builtin id_tup24 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s; vs_t;
  vs_a1; vs_a2; vs_a3; vs_a4] NoDef.
Definition ts_tuple25 : tysymbol_c := mk_ts_builtin id_tup25 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s; vs_t;
  vs_a1; vs_a2; vs_a3; vs_a4; vs_a5] NoDef.
Definition ts_tuple26 : tysymbol_c := mk_ts_builtin id_tup26 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s; vs_t;
  vs_a1; vs_a2; vs_a3; vs_a4; vs_a5; vs_a6] NoDef.
Definition ts_tuple27 : tysymbol_c := mk_ts_builtin id_tup27 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s; vs_t;
  vs_a1; vs_a2; vs_a3; vs_a4; vs_a5; vs_a6; vs_a7] NoDef.
Definition ts_tuple28 : tysymbol_c := mk_ts_builtin id_tup28 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s; vs_t;
  vs_a1; vs_a2; vs_a3; vs_a4; vs_a5; vs_a6; vs_a7; vs_a8] NoDef.
Definition ts_tuple29 : tysymbol_c := mk_ts_builtin id_tup29 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s; vs_t;
  vs_a1; vs_a2; vs_a3; vs_a4; vs_a5; vs_a6; vs_a7; vs_a8; vs_a9] NoDef.
Definition ts_tuple30 : tysymbol_c := mk_ts_builtin id_tup30 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s; vs_t;
  vs_a1; vs_a2; vs_a3; vs_a4; vs_a5; vs_a6; vs_a7; vs_a8; vs_a9; vs_b0] NoDef.
Definition ts_tuple31 : tysymbol_c := mk_ts_builtin id_tup31 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s; vs_t;
  vs_a1; vs_a2; vs_a3; vs_a4; vs_a5; vs_a6; vs_a7; vs_a8; vs_a9; vs_b0; vs_b1] NoDef.
  (*Terrible hack, but EasyCrypt needs a few more*)
Definition ts_tuple33 : tysymbol_c := mk_ts_builtin id_tup33 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s; vs_t;
  vs_a1; vs_a2; vs_a3; vs_a4; vs_a5; vs_a6; vs_a7; vs_a8; vs_a9; vs_b0; vs_b1; vs_b2; vs_b3] NoDef.
Definition ts_tuple36 : tysymbol_c := mk_ts_builtin id_tup36 [vs_a; vs_b; vs_c; vs_d; vs_e; vs_f; vs_g; 
  vs_h; vs_i; vs_j; vs_k; vs_l; vs_m; vs_n; vs_o; vs_p; vs_q; vs_r; vs_s; vs_t;
  vs_a1; vs_a2; vs_a3; vs_a4; vs_a5; vs_a6; vs_a7; vs_a8; vs_a9; vs_b0; vs_b1;
  vs_b2; vs_b3; vs_b4; vs_b5; vs_b6] NoDef.

Definition ts_tuple_list : list tysymbol_c :=  [ts_tuple0; ts_tuple1; ts_tuple2; ts_tuple3; ts_tuple4; ts_tuple5; ts_tuple6; ts_tuple7; 
  ts_tuple8; ts_tuple9; ts_tuple10; ts_tuple11; ts_tuple12; ts_tuple13; ts_tuple14; ts_tuple15; ts_tuple16;
  ts_tuple17; ts_tuple18; ts_tuple19; ts_tuple20; ts_tuple21; ts_tuple22; ts_tuple23; ts_tuple24;
  ts_tuple25; ts_tuple26; ts_tuple27; ts_tuple28; ts_tuple29; ts_tuple30].

(*Doesn't work with tuple > 30*)
Definition ts_tuple (n: CoqBigInt.t) : errorM tysymbol_c :=
  match IntFuncs.big_nth ts_tuple_list n with
  | Some x => err_ret x
  | None => 
    if CoqBigInt.eqb n CoqBigInt.thirtyone then err_ret ts_tuple31
    else if CoqBigInt.eqb n CoqBigInt.thirtythree then err_ret ts_tuple33
    else if CoqBigInt.eqb n CoqBigInt.thirtysix then err_ret ts_tuple36  
    else throw (Invalid_argument ("Tuple cannot be larger than 30, it is " ++ CoqBigInt.to_string n))
  end.

Local Open Scope errst_scope.

Definition ty_tuple tyl : errState (hashcons_ty ty_c) ty_c := 
  ts <- errst_lift2 (ts_tuple (IntFuncs.int_length tyl)) ;;
  errst_lift1 (ty_app1 ts tyl).

Definition is_ts_tuple ts : errorM bool := 
  (ts1 <- (ts_tuple (int_length (ts_args_of ts))) ;;
  err_ret (ts_equal ts ts1))%err.

(*Only works up to 20 - need to change?*)
Definition is_ts_tuple_id (i: ident) : option CoqBigInt.t :=
  (find_index id_equal id_tup_list i).

(*Old, stateful version, works but we have to thread state through ADT trans and forward*)
(* 
(*We create the tuple type symbols and types as needed,
  storing in a hash table*)
(*We have 2 hash tables: int -> symbol and symbol -> int*)
Module TysymbolT <: CoqExthtbl.ModTySimpl.
Definition t := tysymbol_c.
End TysymbolT.
Module BigIntT <: CoqExthtbl.ModTySimpl.
Definition t := CoqBigInt.t.
End BigIntT.
Module IdentTag2 := CoqWstdlib.MakeTagged IdentTag.
Module TupIds := CoqExthtbl.MakeExthtbl(CoqWstdlib.BigIntTag) (TysymbolT).
Module TupNames := CoqExthtbl.MakeExthtbl IdentTag2
  BigIntT.

Definition ts_tuple_ids := TupNames.create CoqInt.one.
Definition tuple_memo := TupIds.create CoqInt.one.

(*CoqBig int for now, but need function to turn
  to string*)

(*NOTE: for now, we memoize manually because everything is in
  the state monad
  type is st (ctr * (TupNames * TupIds))
  Not ideal TODO reduce boilerplate*)
Definition ts_tuple : CoqBigInt.t -> st _ tysymbol_c :=
  fun (n: CoqBigInt.t) =>
    o <- (st_lift2 (st_lift2 (TupIds.find_opt n))) ;;
    match o with
    | Some v => st_ret v
    | None =>
      (*Create n fresh type variables*)
      (*Order doesn't matter, so we can reverse*)
      let vl := foldl_st (fun l _ => 
        h <- create_tvsymbol (IdentDefs.id_fresh1 "a") ;;
        st_ret (h :: l)
      ) (iota n) nil : ctr (list tvsymbol) in
      l <- (st_lift1 vl) ;;
      i <- (st_lift1 (id_register 
        (id_fresh1 ("tuple" ++ CoqBigInt.to_string n)))) ;;
      let ts :=  mk_ts_builtin i l NoDef in (*NOTE: know no error*)
      _ <- st_lift2 (st_lift1 (TupNames.add (ts_name_of ts) n)) ;;
      _ <- st_lift2 (st_lift2 (TupIds.add n ts)) ;;
      st_ret ts
    end.

(*Types are getting worse:
  st ((ctr * (TupNames * TupIds)) * hashcons ty)*)
Definition ty_tuple (l: list ty_c) : st _ ty_c :=
  s <- st_lift1 (ts_tuple (int_length l)) ;;
  st_lift2 (ty_app1 s l). (*Know we won't hit error don't need ty_app*)

(*Different implementation: we just look up in hash table,
  don't call [ts_tuple]. Less state in state monad*)
Definition is_ts_tuple (ts: tysymbol_c) : 
  hash_st CoqBigInt.t tysymbol_c bool :=
  o <- TupIds.find_opt (int_length (ts_args_of ts)) ;;
  match o with
  | None => st_ret false
  | Some t => st_ret (tysymbol_eqb t ts)
  end.

Definition is_ts_tuple_id (i: ident) : hash_st ident CoqBigInt.t 
  (option CoqBigInt.t) :=
  o <- TupNames.find_opt i ;;
  st_ret o. *)

(** {2 Operations on [ty option]} *)
Definition UnexpectedProp := mk_errtype "UnexpectedProp" tt.

Definition oty_type (x: option ty_c) : errorM ty_c :=
  match x with
  | Some t => err_ret t
  | None => throw UnexpectedProp
  end.

Definition oty_equal (o1 o2: option ty_c) : bool :=
  option_eqb ty_equal o1 o2.

Definition oty_hash (o: option ty_c) : CoqBigInt.t :=
  option_fold CoqBigInt.one ty_hash o.

Definition oty_compare (o1 o2: option ty_c) : CoqInt.int :=
  option_compare ty_compare o1 o2.

Definition oty_match (m: Mtv.t ty_c) (o1 o2: option ty_c) : errorHashconsT _ (Mtv.t ty_c) :=
  match o1, o2 with
  | Some ty1, Some ty2 => ty_match m ty1 ty2
  | None, None => errst_ret m
  | _, _ => errst_lift2 (throw UnexpectedProp)
  end.

Definition oty_inst (m: Mtv.t ty_c) (o: option ty_c) : option (hashcons_st _ ty_c) :=
  option_map (ty_inst m) o.

Definition opt_fold {A B: Type} (f: A -> B -> A) (d: A) (o: option B) : A :=
  match o with
  | None => d
  | Some x => f d x
  end.

Definition oty_freevars : Stv.t -> option ty_c -> Stv.t := 
  opt_fold ty_freevars.

Definition oty_cons (l: list ty_c) (o: option ty_c) : list ty_c :=
  opt_fold (fun tl t => t :: tl) l o.

Definition ty_equal_check ty1 ty2 : errorM unit :=
  if negb (ty_equal ty1 ty2) then throw (TypeMismatch (ty1, ty2))
  else err_ret tt.