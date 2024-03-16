Require Import ErrorMonad StateMonad TyDefs.

Definition mk_ty (n: ty_node_c) : ty_c :=
  mk_ty_c n Weakhtbl.dummy_tag.

Definition ty_var (n: tvsymbol) : hashcons_st ty_c :=
  Hsty.hashcons (mk_ty (Tyvar n)).
Definition ty_app1 (s: tysymbol_c) (tl: list ty_c) : hashcons_st ty_c :=
  Hsty.hashcons (mk_ty (Tyapp s tl)).

(*Generic Traversal Functions*)
(*The reason we actually do want hash consing, or else
  the counter grows every time we call one of these functions*)
Definition ty_map (fn: ty_c -> ty_c) (t: ty_c) : hashcons_st ty_c :=
  match ty_node_of t with
  | Tyvar _ => hashcons_ret t
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

(*We want to lift a (list (m A)) to a m (list A) for a monad m.
  We can do this in 3 ways:
  1. Use typeclasses
  2. Give a generic function that takes in bind and return
  3. Write the same function for each monad
  Unfortunately, the first 2 ways give horrible OCaml code
  full of Object.magic and that can easily not compile
  (we need non-prenex polymorphism).
  So we do the third (for now)*)
(*Just so we don't have to write it 3 times*)
(*Of course in OCaml, these all reduce to the identity function*)
Notation listM ret bnd l :=
  (fold_right (fun x acc =>
    bnd (fun h => bnd (fun t => ret (h :: t)) acc) x)
    (ret nil) l).

Definition hashcons_list {K A : Type} (l: list (@hashcons_st K A)) :
  @hashcons_st K (list A) :=
  listM hashcons_ret hashcons_bnd l.

Definition errorM_list {A: Type} (l: list (errorM A)) : errorM (list A) :=
  listM ret bnd l.

Definition ctr_list {A: Type} (l: list (ctr A)) : ctr (list A) :=
  listM ctr_ret ctr_bnd l.

(*NOTE: we do not use a typeclass because the resulting
  OCaml code is not good*)
(*TODO: this will give horrible OCaml code*)
(*Definition listM {m: Type -> Type}
  (ret: forall A, A -> m A)
  (bnd: forall A B, (A -> m B) -> m A -> m B)
  {A : Type} (l: list (m A)) : m (list A) :=
  fold_right (fun x acc =>
    bnd _ _ (fun h => bnd _ _ (fun t => ret _ (h :: t)) acc) x
  ) (ret _ nil) l.

Definition hashcons_list {K A : Type} (l: list (@hashcons_st K A)) :
  @hashcons_st K (list A) :=
  listM (@hashcons_ret K) (@hashcons_bnd K) l.

Definition errorM_list {A: Type} (l: list (errorM A)) : errorM (list A) :=
  listM (@ret) (@bnd) l.*)

(*Traversal Functions on Type Variables*)
Fixpoint ty_v_map (fn: tvsymbol -> ty_c) (t: ty_c) : hashcons_st ty_c :=
  match ty_node_of t with
  | Tyvar v => hashcons_ret (fn v)
  | Tyapp f tl => hashcons_bnd (fun l => ty_app1 f l)
    (hashcons_list (map (ty_v_map fn) tl))
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

(*Monad transformers (kind of)*)
(*TODO: move*)

(*Ok, we do want a monad instance for (errorM (hashcons_st A))
  so we can use listM
  also this is annoying haha*)
(*Problem is doing it generically means OCaml code is bad*)
(*For now, do 1 by 1*)
(*Choose this order: state still exists, may have result*)
(*Basically ExceptT on state monad*)
Definition errorHashT {K : Type} (A: Type) : Type :=
  @hashcons_st K (errorM A).

Definition errorHash_ret {K A: Type} (x: A) : @errorHashT K A :=
  hashcons_ret (ret x).

Definition errorHash_bnd {K A B: Type} (f: A -> errorHashT B) (x: errorHashT A) : 
  @errorHashT K B :=
  hashcons_bnd (fun y =>
    match y with
    | Normal _ z => f z
    | Error _ e => hashcons_ret (Error _ e)
    end) x.

Definition errorHash_lift {K A: Type} (x: @hashcons_st K A) :
  @errorHashT K A :=
  hashcons_bnd (fun s => (hashcons_ret (ret s))) x.

(*TODO: am I doing this right?*)
Definition errorHash_lift2 {K A: Type} (x: errorM A) :
  @errorHashT K A :=
  fun s => (s, x). 

Definition errorHash_list {K A: Type} (l: list (@errorHashT K A)) :
 @errorHashT K (list A) :=
  listM errorHash_ret errorHash_bnd l.

Fixpoint ty_v_map_err (fn: tvsymbol -> errorM ty_c) (t: ty_c) :
  errorHashT ty_c :=
  match ty_node_of t with
  | Tyvar v => errorHash_lift2 (fn v)
  | Tyapp f tl => errorHash_bnd (fun l =>
      errorHash_lift (ty_app1 f l)
  ) (errorHash_list (map (ty_v_map_err fn) tl))
  end.

Definition ty_full_inst (m: Mtv.t ty_c) (t: ty_c) : errorHashT ty_c:=
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

(*TODO: replace before*)
Fixpoint int_length {A: Type} (l: list A) : CoqBigInt.t :=
  match l with
  | nil => CoqBigInt.zero
  | _ :: t => CoqBigInt.succ (int_length t)
  end.

Require Import Ident.

Definition DuplicateTypeVar (t: tvsymbol) : errtype := 
  mk_errtype t.

(*Note: fold right, not left*)
(*Version that can be used in nested recursive defs*)
Definition fold_errorM' := fun {A B: Type} (f: A -> B -> errorM A) =>
  fix fold_errorM (l: list B) (x: A) {struct l} :=
  match l with
  | nil => ret x
  | h :: t => bnd (fun i => f i h) (fold_errorM t x)
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
  ty_v_fold_err (fun acc v => bnd (fun i => ret (i && acc)) (pr v)) true t.

Definition UnboundTypeVar (t: tvsymbol) : errtype := 
  mk_errtype t.

Definition ignore {A: Type} (x: errorM A) : errorM unit :=
  bnd (fun _ => ret tt) x.

Definition null {A: Type} (l: list A) : bool :=
  match l with
  | nil => true
  | _ => false
  end.

Definition IllegalTypeParameters : errtype := mk_errtype tt.
Definition EmptyRange : errtype := mk_errtype tt.
Definition BadFloatSpec : errtype := mk_errtype tt.

Definition create_tysymbol (name: preid) (args: list tvsymbol) (d: type_def ty_c) (*: tysymbol_c*)
  : errorM (ctr tysymbol_c) :=
  let add (s: Stv.t) (v: tvsymbol) := Stv.add_new (DuplicateTypeVar v) v s in
  let s1 := fold_errorM' add args Stv.empty in
  let check (v: tvsymbol) : errorM bool := bnd 
    (fun m => if Stv.mem v m then ret true 
      else throw (UnboundTypeVar v)) s1 in
  let c: errorM unit :=
    match d with
    | NoDef => ret tt
    | Alias d' => 
      ignore (ty_v_all_err check d')
    | Range ir =>
      if negb (null args) then
        throw IllegalTypeParameters
      else if CoqBigInt.lt ir.(Number.ir_upper) ir.(Number.ir_lower)
        then throw EmptyRange
      else ret tt
    | Float fp => if negb (null args) then
        throw IllegalTypeParameters
      else if CoqBigInt.lt fp.(Number.fp_exponent_digits) CoqBigInt.one ||
        CoqBigInt.lt (fp.(Number.fp_significand_digits)) CoqBigInt.one then
        throw BadFloatSpec
      else ret tt
    end in
  bnd (fun _ => ret (mk_ts name args d)) c.

(*Returns map of type variables to elements in list tl*)
Definition ts_match_args {A: Type} (s: tysymbol_c) (tl: list A) : 
  errorM (Mtv.t A) :=
  match fold_right2 Mtv.add (ts_args_of s) tl Mtv.empty with
  | Some m => ret m
  | None => throw (BadTypeArity (s, int_length tl))
  end.

Definition ty_match_args (t: ty_c) : errorM (Mtv.t ty_c) :=
  match ty_node_of t with
  | Tyapp s tl => ts_match_args s tl
  | _ => throw (Invalid_argument "Ty.ty_match_args")
  end.

Definition ty_app (s: tysymbol_c) (tl: list ty_c) : errorHashT ty_c :=
  match ts_def_of s with
  | Alias t => errorHash_bnd 
    (fun m => ty_full_inst m t) 
    (errorHash_lift2 (ts_match_args s tl))
  | _ =>
    if negb (CoqBigInt.eqb (int_length (ts_args_of s)) (int_length tl)) then
      errorHash_lift2 (throw (BadTypeArity (s, int_length tl)))
    else errorHash_lift (ty_app1 s tl)
  end.


(* symbol-wise map/fold *)
Fixpoint ty_s_map (fn: tysymbol_c -> tysymbol_c) (t: ty_c) : errorHashT ty_c :=
  match ty_node_of t with
  | Tyvar _ => errorHash_ret t
  | Tyapp f tl => errorHash_bnd (fun l => ty_app (fn f) l)
    (errorHash_list (map (ty_s_map fn) tl))
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

(*TODO: very bad*)
Definition ty_mapM (fn: ty_c -> hashcons_st ty_c) (t: ty_c) : hashcons_st ty_c :=
  match ty_node_of t with
  | Tyvar _ => hashcons_ret t
  | Tyapp f tl => hashcons_bnd (fun l => ty_app1 f l) (hashcons_list (map fn tl))
  end.

(*TODO: why does this pass Coq's termination checker?*)
(*Idea: instantiate type variables from the map*)
Fixpoint ty_inst (s: Mtv.t ty_c) (t: ty_c) : hashcons_st ty_c :=
  match ty_node_of t with
  | Tyvar n => hashcons_ret (Mtv.find_def _ t n s)
  | _ => ty_mapM (ty_inst s) t
  end.

Definition Exit : errtype := mk_errtype tt.

(*Version with exceptions*)
(*Write in strange way so Coq can use in nested recursion*)
Definition fold_right2_error := fun {A B C: Type} (f: C -> A -> B -> errorM C) =>
  fix fold_right2_error (l1: list A) (l2: list B) (accu: C) {struct l1} : errorM C :=
  match l1, l2 with
  | nil, nil => ret accu
  | a1 :: l1, a2 :: l2 => 
    bnd (fun x => f x a1 a2) (fold_right2_error l1 l2 accu)
  | _, _ => throw (Invalid_argument "fold_right2")
  end.

Definition TypeMismatch (t: ty_c * ty_c) : errtype := mk_errtype t.

(*Idea: when we have variable: check to see if it is in map
  If so, must be mapped to ty2 or else throw exception*)
(*We add an extra parameter in a bit of a hack so that 
  we throw the exception that the higher-level interface
  expects (since we don't have try/catch)*)
Fixpoint ty_match_aux (onerr: ty_c * ty_c) 
  (s: Mtv.t ty_c) (ty1 ty2: ty_c) 
   : errorM (Mtv.t ty_c) :=

  match ty_node_of ty1, ty_node_of ty2 with
  | Tyapp f1 l1, Tyapp f2 l2 =>
    if ts_equal f1 f2 then
    fold_right2_error (ty_match_aux onerr) l1 l2 s
    else throw (TypeMismatch onerr)
  | Tyvar n1, _ => 
    (*We are not using Mtv.change because there is an
      exception in the function (so the types do not match)
      Instead, we will search manually and throw an exception if needed*)
    match Mtv.find_opt _ n1 s with
    | Some ty3 => if ty_equal ty3 ty2 then ret s else
      throw (TypeMismatch onerr)
    | None => ret (Mtv.add n1 ty2 s)
    end
  | _, _ => throw (TypeMismatch onerr)
  end.

Definition ty_match  (s: Mtv.t ty_c) (ty1 ty2: ty_c) : errorHashT (Mtv.t ty_c) :=
  hashcons_bnd (fun t1 => hashcons_ret (ty_match_aux (t1, ty2) s ty1 ty2)) (ty_inst s ty1).


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
Definition ty_func (ty_a ty_b: ty_c) : hashcons_st ty_c :=
  ty_app1 ts_func [ty_a; ty_b].

Definition ty_pred (ty_a : ty_c) : hashcons_st ty_c := 
  hashcons_bnd (fun t =>
    ty_app1 ts_func [ty_a; t]) ty_bool.

(*For now, skip tuples*)

(*Again, know that [create_tysymbol] succeds so use [mk_ts]*)
(*NOTE: no memoization so this will increase counter each time
  tuple is called (not ideal maybe implement TODO)*)
(*TODO: maybe just build in tuples up to 17 elements or
  so (what they assume) - this would avoid state issues and
  make things just as fast*)
(*Definition ts_tuple (n: CoqBigInt.t) :=
  (*Create symbols a1, a2, ..., an*)
  let vl := map (fun _ => create_tvsymbol (id_fresh "a")) (CoqInt.list_init n (fun _ => tt)) in
  let ts := ctr_bnd (fun l => mk_ts (id_fresh ("tuple" ++ CoqInt.string_of_int n)) l NoDef)
    (ctr_list vl) in
  ts.*)
(*
Definition ty_tuple (tyl: list ty_c) :=
  ctr_bnd (fun ts => ty_app1 ts tyl)
    (ts_tuple (int_length2 _ tyl)).*)


(** {2 Operations on [ty option]} *)
Definition UnexpectedProp := mk_errtype tt.

(*Skip [oty_type]*)

Definition oty_equal (o1 o2: option ty_c) : bool :=
  option_eqb ty_equal o1 o2.

Definition option_fold {A B: Type} (none: A) (some: B -> A) (o: option B) : A :=
  match o with
  | None => none
  | Some x => some x
  end.

Definition oty_hash (o: option ty_c) : CoqBigInt.t :=
  option_fold CoqBigInt.one ty_hash o.

(*Skip [oty_compare]*)
Definition oty_match (m: Mtv.t ty_c) (o1 o2: option ty_c) : errorHashT (Mtv.t ty_c) :=
  match o1, o2 with
  | Some ty1, Some ty2 => ty_match m ty1 ty2
  | None, None => errorHash_ret m
  | _, _ => errorHash_lift2 (throw UnexpectedProp)
  end.

Definition oty_inst (m: Mtv.t ty_c) (o: option ty_c) : option (hashcons_st ty_c) :=
  option_map (ty_inst m) o.

Definition opt_fold {A B: Type} (f: A -> B -> A) (d: A) (o: option B) : A :=
  match o with
  | None => d
  | Some x => f d x
  end.

Definition oty_freevars : Stv.t -> option ty_c -> Stv.t := 
  opt_fold ty_freevars.

Definition oty_cons : list ty_c -> option ty_c -> list ty_c :=
  opt_fold (fun tl t => t :: tl).

Definition ty_equal_check ty1 ty2 : errorM unit :=
  if negb (ty_equal ty1 ty2) then throw (TypeMismatch (ty1, ty2))
  else ret tt.