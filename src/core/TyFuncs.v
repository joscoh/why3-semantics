Require Import Monads TyDefs IntFuncs.
From ExtLib Require Import Monads.
Import MonadNotations.
Local Open Scope monad_scope.

Definition mk_ty (n: ty_node_c) : ty_c :=
  mk_ty_c n CoqWeakhtbl.dummy_tag.

Definition ty_var (n: tvsymbol) : hashcons_st _ ty_c :=
  Hsty.hashcons (mk_ty (Tyvar n)).
Definition ty_app1 (s: tysymbol_c) (tl: list ty_c) : hashcons_st _ ty_c :=
  Hsty.hashcons (mk_ty (Tyapp s tl)).

(*Generic Traversal Functions*)
(*The reason we actually do want hash consing, or else
  the counter grows every time we call one of these functions*)
Definition ty_map (fn: ty_c -> ty_c) (t: ty_c) : hashcons_st _ ty_c :=
  match ty_node_of t with
  | Tyvar _ => st_ret t
  | Tyapp f tl => ty_app1 f (map fn tl)
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
  match ty_node_of t with
  | Tyvar v => errst_lift2 (fn v)
  | Tyapp f tl =>
    l <-- errst_list (map (ty_v_map_err fn) tl) ;;;
    errst_lift1 (ty_app1 f l)
  end.

Definition ty_full_inst (m: Mtv.t ty_c) (t: ty_c) : errorHashconsT ty_c ty_c:=
  ty_v_map_err (fun v => Mtv.find _ v m) t.

Definition ty_freevars (s: Stv.t) (t: ty_c) : Stv.t :=
  ty_v_fold Stv.add_left s t.

Definition ty_closed (t: ty_c) : bool :=
  ty_v_all (fun _ => false) t.

(*Smart constructors*)

Definition mk_errtype {A: Type} (x: A) : errtype :=
  {| errargs := A; errdata := x|}.

Definition BadTypeArity (t: tysymbol_c * CoqBigInt.t) : errtype := 
  mk_errtype t.

Require Import IdentDefs.

Definition DuplicateTypeVar (t: tvsymbol) : errtype := 
  mk_errtype t.

(*Note: fold right, not left*)
(*Version that can be used in nested recursive defs*)
Definition fold_errorM' := fun {A B: Type} (f: A -> B -> errorM A) =>
  fix fold_errorM (l: list B) (x: A) {struct l} :=
  match l with
  | nil => err_ret x
  | h :: t =>
    i <-- fold_errorM t x ;;
    f i h
  end.

(*TODO: replace with this?*)
Fixpoint ty_v_fold_err {A: Type} (fn: A -> tvsymbol -> errorM A) (acc: A)
  (t: ty_c) {struct t} : errorM A :=
  match ty_node_of t with
  | Tyvar v => fn acc v
  | Tyapp _ tl => fold_errorM' (ty_v_fold_err fn) tl acc
  end.

Definition ty_v_all_err (pr: tvsymbol -> errorM bool) (t: ty_c) : 
  errorM bool :=
  ty_v_fold_err (fun acc v => 
    i <-- pr v ;;
    err_ret (i && acc)) true t.

Definition UnboundTypeVar (t: tvsymbol) : errtype := 
  mk_errtype t.

Definition IllegalTypeParameters : errtype := mk_errtype tt.
Definition EmptyRange : errtype := mk_errtype tt.
Definition BadFloatSpec : errtype := mk_errtype tt.

Definition create_tysymbol (name: preid) (args: list tvsymbol) (d: type_def ty_c) (*: tysymbol_c*)
  : errorM (ctr tysymbol_c) :=
  let add (s: Stv.t) (v: tvsymbol) := Stv.add_new (DuplicateTypeVar v) v s in
  let s1 := fold_errorM' add args Stv.empty in
  let check (v: tvsymbol) : errorM bool := 
    m <-- s1 ;;
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
      else if CoqBigInt.lt ir.(CoqNumber.ir_upper) ir.(CoqNumber.ir_lower)
        then throw EmptyRange
      else err_ret tt
    | Float fp => if negb (null args) then
        throw IllegalTypeParameters
      else if CoqBigInt.lt fp.(CoqNumber.fp_exponent_digits) CoqBigInt.one ||
        CoqBigInt.lt (fp.(CoqNumber.fp_significand_digits)) CoqBigInt.one then
        throw BadFloatSpec
      else err_ret tt
    end in
  _ <-- c ;;
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
    m <-- (errst_lift2 (ts_match_args s tl)) ;;;
    ty_full_inst m t
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
    l <-- (errst_list (map (ty_s_map fn) tl)) ;;;
    ty_app (fn f) l
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
Local Open Scope monad_scope (*TODO: fix scopes*).
(*TODO: very bad*)
Definition ty_mapM (fn: ty_c -> hashcons_st _ ty_c) (t: ty_c) : hashcons_st _ ty_c :=
  match ty_node_of t with
  | Tyvar _ => st_ret t
  | Tyapp f tl => 
    l <- st_list (map fn tl) ;;
    ty_app1 f l
end.

(*TODO: why does this pass Coq's termination checker?*)
(*Idea: instantiate type variables from the map*)
Fixpoint ty_inst (s: Mtv.t ty_c) (t: ty_c) : hashcons_st _ ty_c :=
  match ty_node_of t with
  | Tyvar n => st_ret (Mtv.find_def _ t n s)
  | _ => ty_mapM (ty_inst s) t
  end.

Definition Exit : errtype := mk_errtype tt.

(*Version with exceptions*)
(*Write in strange way so Coq can use in nested recursion*)
Definition fold_right2_error := fun {A B C: Type} (f: C -> A -> B -> errorM C) =>
  fix fold_right2_error (l1: list A) (l2: list B) (accu: C) {struct l1} : errorM C :=
  match l1, l2 with
  | nil, nil => err_ret accu
  | a1 :: l1, a2 :: l2 => 
    x <-- fold_right2_error l1 l2 accu ;;
    f x a1 a2
  | _, _ => throw (Invalid_argument "fold_right2")
  end.

Definition TypeMismatch (t: ty_c * ty_c) : errtype := mk_errtype t.

(*Idea: when we have variable: check to see if it is in map
  If so, must be mapped to ty2 or else throw exception*)
(*We add an extra parameter in a bit of a hack so that 
  we throw the exception that the higher-level interface
  expects (since we don't have try/catch)*)
Fixpoint ty_match_aux (err1 err2: ty_c) 
  (s: Mtv.t ty_c) (ty1 ty2: ty_c) 
   : errorM (Mtv.t ty_c) :=

  match ty_node_of ty1, ty_node_of ty2 with
  | Tyapp f1 l1, Tyapp f2 l2 =>
    if ts_equal f1 f2 then
    fold_right2_error (ty_match_aux err1 err2) l1 l2 s
    else throw (TypeMismatch (err1, err2))
  | Tyvar n1, _ => 
    (*We are not using Mtv.change because there is an
      exception in the function (so the types do not match)
      Instead, we will search manually and throw an exception if needed*)
    match Mtv.find_opt _ n1 s with
    | Some ty3 => if ty_equal ty3 ty2 then err_ret s else
      throw (TypeMismatch (err1, err2))
    | None => err_ret (Mtv.add n1 ty2 s)
    end
  | _, _ => throw (TypeMismatch (err1, err2))
  end.

Definition ty_match  (s: Mtv.t ty_c) (ty1 ty2: ty_c) : errorHashconsT _ (Mtv.t ty_c) :=
  t1 <-- (errst_lift1 (ty_inst s ty1)) ;;;
  errst_lift2 (ty_match_aux t1 ty2 s ty1 ty2).


(* built-in symbols *)


Definition mk_ts_builtin (name: ident) (args: list tvsymbol) (d: type_def ty_c) : 
  tysymbol_c := mk_ts_c name args d.


(*TODO: should probably change create_tysymbol to different
  monad order*)
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
Definition ty_int := ty_app1 ts_int nil.
Definition ty_real := ty_app1 ts_real nil.
Definition ty_bool := ty_app1 ts_bool nil.
Definition ty_str := ty_app1 ts_str nil.

Definition create_builtin_tvsymbol (i: ident) : tvsymbol :=
  {| tv_name := i|}.

Definition ts_func :=
  let tv_a := create_builtin_tvsymbol id_a in
  let tv_b := create_builtin_tvsymbol id_b in
  mk_ts_builtin id_fun [tv_a; tv_b] NoDef.

(*We know that [ty_app] always succeeds here*)
Definition ty_func (ty_a ty_b: ty_c) : hashcons_st _ ty_c :=
  ty_app1 ts_func [ty_a; ty_b].

Definition ty_pred (ty_a : ty_c) : hashcons_st _ ty_c := 
  t <- ty_bool ;;
  ty_app1 ts_func [ty_a; t].

(*Tuples*)

(*We create the tuple type symbols and types as needed,
  storing in a hash table*)
(*We have 2 hash tables: int -> symbol and symbol -> int*)
Module TysymbolT <: CoqExthtbl.TyMod.
Definition t := tysymbol_c.
End TysymbolT.
Module BigIntT <: CoqExthtbl.TyMod.
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

(*TODO: move*)
(*A fold left*)
Definition fold_left_st := fun {S1 A B: Type} (f: A -> B -> st S1 A) =>
  fix fold_left_st (l: list B) (x: A) {struct l} :=
  match l with
  | nil => st_ret x
  | h :: t => j <- f x h ;;
              fold_left_st t j
  end.

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
      let vl := fold_left_st (fun l _ => 
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
  st_ret o.

(** {2 Operations on [ty option]} *)
Definition UnexpectedProp := mk_errtype tt.

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